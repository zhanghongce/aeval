#include <stdint.h>

extern uint8_t *nd_uint8_ptr (void);
extern int64_t nd(void);
extern uint64_t nd_uint64_t(void);

static uint8_t* sea_base;
static uint8_t* sea_ptr;
static int64_t sea_offset;
static int64_t sea_size;

extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);

#define assume __VERIFIER_assume
__attribute__((always_inline)) void assert  (int v)  { if (!v) __VERIFIER_error (); }

__attribute__((used)) void sea_abc_assert_valid_ptr (uint8_t *base, int64_t offset);
__attribute__((used)) void sea_abc_assert_valid_offset (int64_t offset, int64_t size);
__attribute__((used)) void sea_abc_log_ptr (uint8_t *base, int64_t offset);
__attribute__((used)) void sea_abc_alloc (uint8_t *base, int64_t size);
__attribute__((used)) void sea_abc_init(void);
  
/*
 * checks that base + offset is a valid pointer
 * insert after every load/store when size is unknown
 * base is a base pointer of some gep
 * offset is the computed offset _Should be adjusted for used size if needed_
 */

void sea_abc_assert_valid_ptr (uint8_t *base, int64_t offset)
{
  if (!sea_ptr) return;

  if (base == sea_base)
  {
   assert (offset >= 0 );
   assert (offset <= sea_size);
  }
  else if (base == sea_ptr)
  {
    assert (sea_offset + offset >= 0);
    assert (sea_offset + offset <= sea_size);
  }
}

/**
 * insert after every load/store when offset and size are known
 * offset is the computed offset
 * size is a constant size
 */
void sea_abc_assert_valid_offset (int64_t offset, int64_t size)
{
  if (!sea_ptr) return;
  
   assert (offset <= size);
  /* TODO: do not know how to check for underflow */
}

/**
 * insert after every p = gep(base, offset), if p is used indirectly
 * base - the base argument to gep
 * offset - the computed offset from gep + used_size
 */
void sea_abc_log_ptr (uint8_t *base, int64_t offset)
{
  if (nd()) return;
  
  if (sea_ptr == base)
  {
    sea_ptr = nd_uint8_ptr();
    /* trick alias analysis */
    assume (sea_ptr == sea_ptr + offset);
  }
}

/**
 * insert after every allocation instruction
 * base - pointer to allocated buffer
 * size - the size of the allocated buffer
 */
void sea_abc_alloc (uint8_t *base, int64_t size)
{
  if (sea_ptr == 0 && sea_base == base)
  {
    assume (sea_size == size);
    sea_ptr = nd_uint8_ptr();
    assume (sea_ptr == sea_base);
  }
  else
    assume (sea_base + sea_size < base);
}

void sea_abc_init(void)
{
  sea_base = nd_uint8_ptr ();
  assume (sea_base > 0);
  sea_size = nd ();
  assume (sea_size >= 0); 
  sea_offset = 0;
  sea_ptr = 0;
}
