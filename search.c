#include <assert.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <zlib.h>

#include "roaring.h"

#define MIN(x,y) ((x) < (y) ? (x) : (y))

#define array_list(T) struct { size_t size; size_t capacity; T *restrict elements; }
#define array_list_free(list) free((list).elements)
#define array_list_add(list, e) do {                                    \
        if ((list).size == (list).capacity) {                           \
            (list).capacity = (list).capacity * 2 + 1;                  \
            (list).elements = realloc(                                  \
                (list).elements,                                        \
                sizeof(typeof((list).elements[0])) * (list).capacity    \
            );                                                          \
        }                                                               \
        (list).elements[(list).size++] = e;                             \
    } while (0)

struct dictionary {
	size_t length;
	uint8_t **summary;
};

static uint32_t read_uint32_le(const uint8_t *p)
{
	uint32_t val;
	memcpy(&val, p, sizeof(val));
	return val;
}

static void write_uint32_le(uint8_t *p, uint32_t val)
{
	memcpy(p, &val, sizeof(val));
}

static int keycmp(const uint8_t *a, size_t la, const uint8_t *b, size_t lb)
{
	size_t len = MIN(la, lb);
	int cmp = memcmp(a, b, len);

	if (cmp || la == lb) {
		return cmp;
	}

	return la - lb;
}

struct dictionary *dictionary_from_blob(uint8_t *blob, size_t size)
{
	array_list(uint8_t *) references = {};
	struct dictionary *dict = malloc(sizeof(struct dictionary));

	for (size_t i = 0; i < size; ) {
		array_list_add(references, blob + i);
		uint32_t key_length = read_uint32_le(blob + i);
		uint32_t value_length = read_uint32_le(blob + i + 4);
		i += 4 + 4 + key_length + value_length;
	}

	dict->length = references.size;
	dict->summary = references.elements;

	return dict;
}

roaring_bitmap_t *get_bitmap(struct dictionary *dict, char *term)
{
	size_t len = strlen(term);
	int32_t left = 0;
	int32_t right = dict->length - 1;
	int cmp = 0;

	while (left <= right) {
		int32_t mid = left + (right - left) / 2;
		uint8_t *entry = dict->summary[mid];

		uint32_t key_length = read_uint32_le(entry);
		uint32_t val_length = read_uint32_le(entry + 4);
		cmp = keycmp(entry + 8, key_length, (uint8_t *) term, len);

		if (cmp == 0)
			return roaring_bitmap_portable_deserialize_safe((char *) entry + 8 + key_length, val_length);

		if (cmp < 0)
			left = mid + 1;
		else
			right = mid - 1;
	}

	return NULL;
}

roaring_bitmap_t *execute_query(struct dictionary *dictionary, char *query)
{
	roaring_bitmap_t *ret = NULL;
	roaring_bitmap_t *b;

	for (char *part = query; ; part = NULL)  {
		char *token = strtok(part, ",");
		if (token == NULL)
			break;

		b = get_bitmap(dictionary, token);

		if (b && !ret) {
			ret = b;
		} else if (b && ret) {
			roaring_bitmap_and_inplace(ret, b);
			roaring_bitmap_free(b);
		} else if (!b && ret) {
			roaring_bitmap_clear(ret);
			break;
		} else if (!b && !ret) {
			break;
		}
	}

	if (!ret) {
		ret = roaring_bitmap_create_with_capacity(0);
	}
	return ret;
}

#define FACTOR 32

struct int_pair {
	uint32_t key;
	uint32_t value;
};

static int dblcmp(uint32_t ka, uint32_t va, uint32_t kb, uint32_t vb)
{
	int cmp = ka - kb;
	if (!cmp) cmp = va - vb;
	return cmp;
}

static int int_pair_keycmp(const struct int_pair *a, const struct int_pair *b)
{
	return dblcmp(a->key, a->value, b->key, b->value);
}

static int int_pair_valcmp(const struct int_pair *a, const struct int_pair *b)
{
	return dblcmp(a->value, a->key, b->value, b->key);
}

struct cbtree_node {
	struct {
		uint64_t min_val;
		uint32_t min_key;
	};
	union {
		roaring_bitmap_t *covering_bitmap;
		uint32_t value;
	};
	uint8_t is_leaf;
};

struct cbtree_level {
	uint32_t num_nodes;
	struct cbtree_node *nodes;
};

struct sort_dictionary {
	uint32_t num_nodes;
	struct int_pair *forward;
	uint32_t num_levels;
	struct cbtree_level *levels;
};

struct sort_dictionary *bitmap_tree_from_values(uint8_t *blob, size_t size)
{
	size_t raw_nodes = size / (2*sizeof(uint32_t));

	uint32_t last_key = 0;
	uint32_t last_val = 0;
	for (size_t i = 0; i < size; i += 8) {
		uint32_t key = read_uint32_le(blob + i) + last_key;
		uint32_t val = read_uint32_le(blob + i + 4) + last_val;
		write_uint32_le(blob + i, key);
		write_uint32_le(blob + i + 4, val);
		last_key = key;
		last_val = val;
	}

	qsort(blob, raw_nodes, sizeof(struct int_pair), (void *) int_pair_valcmp);

	array_list(struct cbtree_level) levels = {};

	struct cbtree_node *node_ptr = malloc(sizeof(struct cbtree_node) * raw_nodes);
	struct cbtree_node *nodes = node_ptr;

	for (size_t i = 0; i < size; ) {
		uint32_t id = read_uint32_le(blob + i);
		i += 4;
		uint32_t val = read_uint32_le(blob + i);
		i += 4;

		*nodes++ = (struct cbtree_node) { .min_val = val, .min_key = id, .is_leaf = 1, .value = id };
	}

	struct cbtree_level level = { .num_nodes = nodes - node_ptr, .nodes = node_ptr };
	array_list_add(levels, level);

	while (levels.elements[levels.size - 1].num_nodes > FACTOR) {
		// Summarize preceding level
		struct cbtree_level *old_level = &levels.elements[levels.size - 1];

		uint32_t num_nodes = (old_level->num_nodes + (FACTOR - 1)) / FACTOR;
		struct cbtree_node *node_ptr = malloc(sizeof(struct cbtree_node) * num_nodes);
		struct cbtree_node *nodes = node_ptr;

		for (uint32_t i = 0; i < num_nodes; i++) {
			uint32_t min_val = old_level->nodes[i*FACTOR].min_val;
			uint32_t min_key = old_level->nodes[i*FACTOR].min_key;
			uint32_t max_lower = MIN(old_level->num_nodes, (i + 1) * FACTOR);
			roaring_bitmap_t *val = roaring_bitmap_create_with_capacity(0);;

			for (uint32_t j = i * FACTOR; j < max_lower; j++) {
				if (old_level->nodes[j].is_leaf) {
					roaring_bitmap_add(val, old_level->nodes[j].value);
				} else {
					roaring_bitmap_lazy_or_inplace(val, old_level->nodes[j].covering_bitmap, 0);
				}
			}

			roaring_bitmap_repair_after_lazy(val);

			*nodes++ = (struct cbtree_node) { .min_val = min_val, .min_key = min_key, .is_leaf = 0, .covering_bitmap = val };
		}

		struct cbtree_level level = { .num_nodes = num_nodes, .nodes = node_ptr };
		array_list_add(levels, level);
	}

	struct int_pair *forward_pairs = (struct int_pair *) blob;
	qsort(forward_pairs, raw_nodes, sizeof(struct int_pair), (void *) int_pair_keycmp);

	struct sort_dictionary *dict = malloc(sizeof(struct sort_dictionary));

	dict->forward = forward_pairs;
	dict->num_nodes = raw_nodes;
	dict->num_levels = levels.size;
	dict->levels = levels.elements;
	
	return dict;
}

struct inline_result {
	uint64_t val;
	uint32_t id;
};

static int inline_result_cmp(const struct inline_result *a, const struct inline_result *b)
{
	int cmp = (a->val - b->val);
	if (!cmp) cmp = (a->id - b->id);
	return cmp;
}

static uint32_t hoare_partition(struct inline_result *list, uint32_t lo, uint32_t hi)
{
	size_t sz = hi - lo + 1;
	uint32_t pivot_index = lo + (rand() % sz);
	struct inline_result pivot = list[pivot_index];

	int32_t i = lo - 1;
	int32_t j = hi + 1;

	while (1) {
		do { i++; } while (inline_result_cmp(&list[i], &pivot) < 0);
		do { j--; } while (inline_result_cmp(&list[j], &pivot) > 0);

		if (i >= j) return j;

		struct inline_result tmp = list[i];
		list[i] = list[j];
		list[j] = tmp;
	}
}

static uint32_t quickselect(struct inline_result *list, uint32_t lo, uint32_t hi, uint32_t k)
{
	if (lo == hi)
		return list[lo].id;

	uint32_t pivot_index = hoare_partition(list, lo, hi);

	if (k <= pivot_index)
		return quickselect(list, lo, pivot_index - 0, k);
	else
		return quickselect(list, pivot_index + 1, hi, k);
}

static roaring_bitmap_t *select_gte(struct sort_dictionary *dict, const roaring_bitmap_t *also_intersect, uint64_t value, uint32_t id)
{
	roaring_bitmap_t *bitmap = roaring_bitmap_create_with_capacity(0);
	int32_t start_pos = 0;

	for (int32_t i = dict->num_levels - 1; i >= 0; i--) {
		struct cbtree_level *level = &dict->levels[i];
		int32_t level_length = level->num_nodes;
		int32_t end_pos = MIN(start_pos + FACTOR, level_length);
		int32_t j = end_pos - 1;

		for (; j >= start_pos; j--) {
			uint64_t min_val = level->nodes[j].min_val;
			uint32_t min_key = level->nodes[j].min_key;
			int cmp = dblcmp(min_val, min_key, value, id);

			if (cmp < 0)
				break;

			if (level->nodes[j].is_leaf) {
				roaring_bitmap_add(bitmap, level->nodes[j].value);
			} else {
				roaring_bitmap_lazy_or_inplace(bitmap, level->nodes[j].covering_bitmap, 0);
			}
		}

		if (j < start_pos) {
			// already consumed the entire set
			break;
		}

		start_pos = j * FACTOR;
	}

	if (also_intersect) {
		roaring_bitmap_and_inplace(bitmap, also_intersect);
	}

	roaring_bitmap_repair_after_lazy(bitmap);

	return bitmap;
}

uint32_t bitmap_select(const roaring_bitmap_t *bitmap, uint32_t index)
{
	uint32_t value;
	roaring_bitmap_select(bitmap, index, &value);
	return value;
}

uint64_t lookup_sort_value(struct sort_dictionary *dict, uint32_t id)
{
	int32_t left = 0;
	int32_t right = dict->num_nodes - 1;

	while (left <= right) {
		int32_t mid = left + (right - left) / 2;

		if (dict->forward[mid].key == id)
			return dict->forward[mid].value;

		if (dict->forward[mid].key < id)
			left = mid + 1;
		else
			right = mid - 1;
	}

	abort();
}

static uint32_t bitmap_quickselect(struct sort_dictionary *dict, const roaring_bitmap_t *results, uint32_t cardinality, uint32_t k)
{
	if (cardinality <= 1) {
		// Base case: kth element reached
		return bitmap_select(results, 0);
	}

	if (cardinality <= 16384) {
		// Fall back to normal quickselect for faster resolution of the base case
		roaring_uint32_iterator_t *iter = roaring_create_iterator(results);
		struct inline_result *buf = malloc(sizeof(struct inline_result) * cardinality);

		for (size_t i = 0; i < cardinality; i++) {
			roaring_read_uint32_iterator(iter, &buf[i].id, 1);
			buf[i].val = lookup_sort_value(dict, buf[i].id);
		}

		uint32_t final = quickselect(buf, 0, cardinality - 1, k);

		roaring_free_uint32_iterator(iter);
		free(buf);

		return final;
	}

	uint32_t pivot_index = rand() % cardinality;
	uint32_t pivot_id = bitmap_select(results, pivot_index);
	uint32_t pivot_value = lookup_sort_value(dict, pivot_id);

	roaring_bitmap_t *right_results = select_gte(dict, results, pivot_value, pivot_id);
	roaring_bitmap_t *left_results = roaring_bitmap_andnot(results, right_results);

	uint32_t right_count = roaring_bitmap_get_cardinality(right_results);
	uint32_t left_count = roaring_bitmap_get_cardinality(left_results);

	if (k < left_count) {
		// Go left, no need to adjust k
		uint32_t final = bitmap_quickselect(dict, left_results, left_count, k);

		roaring_bitmap_free(left_results);
		roaring_bitmap_free(right_results);

		return final;
	} else {
		// Go right, and adjust k
		uint32_t final = bitmap_quickselect(dict, right_results, right_count, k - left_count);

		roaring_bitmap_free(left_results);
		roaring_bitmap_free(right_results);

		return final;
	}
}

roaring_bitmap_t *top_k_results(struct sort_dictionary *dict, const roaring_bitmap_t *results, uint32_t cardinality, uint32_t k)
{
	if (cardinality <= k) {
		return roaring_bitmap_copy(results);
	}

	uint32_t top_kth = bitmap_quickselect(dict, results, cardinality, cardinality - k);
	roaring_bitmap_t *top_k_docs = select_gte(dict, results, lookup_sort_value(dict, top_kth), top_kth);

	return top_k_docs;
}

void yolo_uncompress(void *dst, size_t dstlen, const void *src, size_t srclen)
{
	if (uncompress(dst, &dstlen, src, srclen) != Z_OK) {
		abort();
	}
}

#define MULTIPLE 6364136223846793005ULL
#define ROT 23U

static const uint64_t PI[] = {
    0x243f6a8885a308d3,
    0x13198a2e03707344,
    0xa4093822299f31d0,
    0x082efa98ec4e6c89,
};

static uint64_t _rotl(uint64_t value, int shift)
{
	return (value << shift) | (value >> (sizeof(value)*8 - shift));
}

static uint64_t ahash(uint64_t input, const uint64_t key[static 2])
{
	uint64_t buffer = key[0] ^ PI[0];
	uint64_t pad = key[1] ^ PI[1];

	uint64_t d1 = (input ^ buffer) * MULTIPLE;
	pad = _rotl(pad ^ d1, 8) * MULTIPLE;
	buffer = _rotl(buffer ^ pad, 24);

	int rot = buffer & 63;
	return _rotl((buffer * MULTIPLE) ^ pad, rot);
}

static uint64_t feistel_evaluate(uint64_t input, int left_bits, int right_bits, const uint64_t key[static 2])
{
	uint64_t left_mask = (1ULL << left_bits) - 1;
	uint64_t right_mask = (1ULL << right_bits) - 1;

	uint64_t output = input;

	for (size_t i = 0; i < 4; i++) {
		uint64_t l = (output >> right_bits) & left_mask;
		uint64_t r = output & right_mask;
		uint64_t t = (l ^ ahash(r, key)) & left_mask;

		output = (r << left_bits) | (t & right_mask);
	}

	return output;
}

static uint64_t cycle_walking_fpe(uint64_t input, uint64_t n)
{
	int bits = 64 - __builtin_clzll(n - 1);
	int left_bits = bits >> 1;
	int right_bits = bits - left_bits;

	uint64_t output = input;

	while (true) {
		output = feistel_evaluate(output, left_bits, right_bits, PI + 2);

		if (output < n) {
			return output;
		}
	}
}

uint32_t kth_random_result(const roaring_bitmap_t *results, uint32_t cardinality, uint32_t k)
{
	if (k >= cardinality) {
		return -1;
	}

	return bitmap_select(results, cycle_walking_fpe(k, cardinality));
}
