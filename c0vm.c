/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2023                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t  S;   /* Operand stack of C0 values */
  ubyte       *P;   /* Function body */
  size_t       pc;  /* Program counter */
  c0_value    *V;   /* The local variables */
};

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  /* Variables */
  c0v_stack_t S = c0v_stack_new(); /* Operand stack of C0 values */
  ubyte *P = bc0->function_pool->code;      /* Array of bytes that make up the current function */
  size_t pc = 0;     /* Current location within the current byte array P */
  c0_value *V = xmalloc(sizeof(c0_value) * bc0->function_pool->num_vars) ;   /* Local variables (you won't need this till Task 2) */
  (void) V;      // silences compilation errors about V being currently unused

  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack = stack_new();
  (void) callStack; // silences compilation errors about callStack being currently unused

  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
            P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP: {
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      c0v_push(S,first);
      c0v_push(S,second);
      break;
    }


    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */

    case RETURN: {
      c0_value retval = c0v_pop(S);
      ASSERT(c0v_stack_empty(S));
      c0v_stack_free(S);
      free(V);
    // Another way to print only in DEBUG mode
    //IF_DEBUG(fprintf(stderr, "Returning %d from execute()\n", retval));
      // Free everything before returning from the execute function!
      if(stack_empty(callStack)){
        stack_free(callStack, &free);
      }
      else{ //stack not empty so pop frame
        frame* popped = pop(callStack);
        S = popped->S;
        V = popped->V;
        pc = popped->pc;
        P = popped->P;
        c0v_push(S, retval);
        free(popped);
        break;
      }
      return val2int(retval);
    }


    /* Arithmetic and Logical operations */

    case IADD:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int ret = (val2int(second) + val2int(first));
      c0v_push(S, int2val(ret));
      break;
    }

    case ISUB:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int ret = (val2int(second) - val2int(first));
      c0v_push(S, int2val(ret));
      break;
    }

    case IMUL: {
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int ret = (val2int(second) * val2int(first));
      c0v_push(S, int2val(ret));
      break;
    }

    case IDIV: {
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      if(val2int(first) == 0){
        c0_arith_error("Cannot divide by zero.");
      }
      if(val2int(second) == INT32_MIN && val2int(first) == -1){
        c0_arith_error("Overflow error");
      }
      int ret = (val2int(second) / val2int(first));
      c0v_push(S, int2val(ret));
      break;
    }

    case IREM:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      if(val2int(first) == 0){
        c0_arith_error("Cannot divide by zero.");
      }
      if(val2int(second) == INT32_MIN && val2int(first) == -1){
        c0_arith_error("Overflow error");
      }
      int ret = (val2int(second) % val2int(first));
      c0v_push(S, int2val(ret));
      break;
    }

    case IAND:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int ret = (val2int(second) & val2int(first));
      c0v_push(S, int2val(ret));
      break;
    }

    case IOR:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int ret = (val2int(second) | val2int(first));
      c0v_push(S, int2val(ret));
      break;
    }

    case IXOR:
    {
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int ret = (val2int(second) ^ val2int(first));
      c0v_push(S, int2val(ret));
      break;
    }

    case ISHR:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      if(val2int(first) < 0 || val2int(first) >= 32){
        c0_arith_error("This is not a possible shift");
      }
      int ret = (val2int(second) >> val2int(first));
      c0v_push(S, int2val(ret));
      break; 
    }

    case ISHL:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      if(val2int(first) < 0 || val2int(first) >= 32){
        c0_arith_error("This is not a possible shift");
      }
      int ret = (val2int(second) << val2int(first));
      c0v_push(S, int2val(ret));
      break; 

    }


    /* Pushing constants */

    case BIPUSH:
    {
      pc++;
      int32_t ret = (int32_t)((int8_t)P[pc]);
      c0v_push(S, int2val(ret));
      pc++;
      break;
    }

    case ILDC:{
      pc++;
      int c1 = P[pc] << 8;
      pc++;
      int c2 = P[pc];
      int ret = bc0->int_pool[c1 | c2];
      c0v_push(S, int2val(ret));
      pc++;
      break;
    }

    case ALDC:{
      pc++;
      int c1 = P[pc] << 8;
      pc++;
      int c2 = P[pc];
      c0v_push(S, ptr2val(&bc0->string_pool[c1|c2]));
      pc++;
      break;
    }

    case ACONST_NULL:{
      pc++;
      c0v_push(S, ptr2val(NULL));
      break;
    }


    /* Operations on local variables */

    case VLOAD:{
      pc++;
      c0v_push(S, V[P[pc]]);
      pc++;
      break;
    }

    case VSTORE:{
      pc++;
      V[P[pc]] = c0v_pop(S);
      pc++;
      break;
    }


    /* Assertions and errors */

    case ATHROW:{
      pc++;
      c0_user_error((char*)val2ptr(c0v_pop(S)));
      break;
    }

    case ASSERT:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      if(val2int(second) == 0){
        c0_assertion_failure((char*)val2ptr(first));
      }
      break;
    }


    /* Control flow operations */

    case NOP:{
      pc++;
      break;
    }

    case IF_CMPEQ:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int c1 = P[pc] << 8;
      pc++;
      int c2 = P[pc];
      if(val_equal(first, second)){
        pc = pc + (int16_t)(c1 | c2) - 2;
      }
      else{
        pc++;
      }
      break;
    }

    case IF_CMPNE:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int c1 = P[pc] << 8;
      pc++;
      int c2 = P[pc];
      if(!val_equal(first, second)){
        pc = pc + (int16_t)(c1 | c2) - 2;
      }
      else{
        pc++;
      }
      break;
    }

    case IF_ICMPLT:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int c1 = P[pc] << 8;
      pc++;
      int c2 = P[pc];
      if(val2int(second) < val2int(first)){
        pc = pc + (int16_t)(c1 | c2) - 2;
      }
      else{
        pc++;
      }
      break;
    }

    case IF_ICMPGE:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int c1 = P[pc] << 8;
      pc++;
      int c2 = P[pc];
      if(val2int(second) >= val2int(first)){
        pc = pc + (int16_t)(c1 | c2) - 2;
      }
      else{
        pc++;
      }
      break;
    }

    case IF_ICMPGT:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int c1 = P[pc] << 8;
      pc++;
      int c2 = P[pc];
      if(val2int(second) > val2int(first)){
        pc = pc + (int16_t)(c1 | c2) - 2;
      }
      else{
        pc++;
      }
      break;
    }

    case IF_ICMPLE:{
      pc++;
      c0_value first = c0v_pop(S);
      c0_value second = c0v_pop(S);
      int c1 = P[pc] << 8;
      pc++;
      int c2 = P[pc];
      if(val2int(second) <= val2int(first)){
        pc = pc + (int16_t)(c1 | c2) - 2;
      }
      else{
        pc++;
      }
      break;
    }

    case GOTO:{
      pc++;
      int c1 = P[pc] << 8;
      pc++;
      int c2 = P[pc];
      pc = pc + (int16_t)(c1 | c2) - 2;
      break;
    }


    /* Function call operations: */

    case INVOKESTATIC:{
      pc++;
      uint16_t c1 = (uint16_t)P[pc] << 8;
      pc++;
      uint16_t c2 = (uint16_t)P[pc];
      int16_t c3 = c1|c2;
      struct function_info* v = bc0->function_pool + c3;
      pc++;
      //Store information in a new frame to preserve the state:
      frame* newFrame = xmalloc(sizeof(frame));
      newFrame->S = S;
      newFrame->pc = pc;
      newFrame->V = V;
      newFrame->P = P;
      //Push onto global callStack
      push(callStack, newFrame);
      //"Allocate a new array for its local variables, and 
      //initialize it with the function arguments from the old operand stack"
      V = xcalloc(sizeof(c0_value),v->num_vars);
      int num = v->num_args;
      for(int i = num-1; i >= 0; i--){
        V[i] = c0v_pop(S);
      }
      //"create a new empty operand stack for use in the called function."
      S = c0v_stack_new();
      P = v->code;
      //set the pc to the beginning of the code
      pc = 0;
      break;
    }

    case INVOKENATIVE:
    {
      pc++;
      uint16_t c1 = (uint16_t)P[pc] << 8;
      pc++;
      uint16_t c2 = (uint16_t)P[pc];
      int16_t c3 = c1|c2;
      struct native_info* n = bc0->native_pool + c3;
      pc++;
      //"In order to call this function you have to construct an array of length 
      //n and store arguments v1 through vn at indices 0 through n − 1"
      c0_value* storage = xmalloc(sizeof(c0_value) * n->num_args);
      int num = n->num_args;
      for(int i = num-1; i >= 0; i--){
        assert(!c0v_stack_empty(S));
        storage[i] = c0v_pop(S);
      }
      //"and then invoke the function g on this array. The result has to be 
      //pushed back onto the operand stack"
      native_fn* nativeW = native_function_table[n->function_table_index];
      c0_value result = (*nativeW)(storage);
      c0v_push(S, result);
      free(storage);
      break;
    }
    /* Memory allocation and access operations: */

    case NEW:{
      pc++;
      ubyte s = P[pc];
      pc++;
      c0v_push(S, ptr2val(xmalloc(s * sizeof(char))));
      break;
    }

    case IMLOAD:{
      pc++;
      void* a = val2ptr(c0v_pop(S));
      if(a == NULL){
        c0_memory_error("Null memory error");
      }
      c0v_push(S, int2val(*((int*)a)));
      break;
    }

    case IMSTORE:{
      pc++;
      int x = val2int(c0v_pop(S));
      void* a = val2ptr(c0v_pop(S));
      if(a == NULL){
        c0_memory_error("Null memory error");
      }
      *((int*)a) = x;
      break;
    }

    case AMLOAD:{
      pc++;
      void ** address = val2ptr(c0v_pop(S));
      if(address == NULL){
        c0_memory_error("Null memory error");
      }
      c0v_push(S, ptr2val(*address));
      break;
    }

    case AMSTORE:{
      pc++;
      void * address1 = val2ptr(c0v_pop(S));
      void ** address2 = val2ptr(c0v_pop(S));
      if(address2 == NULL){
        c0_memory_error("Null memory error");
      }
      *address2 = address1;
      break;
    }

    case CMLOAD:{
      pc++;
      void * a = val2ptr(c0v_pop(S));
      if(a == NULL){
        c0_memory_error("Null memory error");
      }
      int x = (int)(*((char*)a));
      c0v_push(S, int2val(x));
      break;
    }

    case CMSTORE:{
      pc++;
      int x = val2int(c0v_pop(S));
      void* a = val2ptr(c0v_pop(S));
      if(a == NULL){
        c0_memory_error("Null memory error");
      }
      *((char*)a) = x & 0x7f;
      break;

    }

    case AADDF:{
      pc++;
      ubyte f = P[pc];
      void* a = val2ptr(c0v_pop(S));
      if(a == NULL){
        c0_memory_error("Null memory error");
      }
      c0v_push(S, ptr2val((void*)((char*)a+f)));
      pc++;
      break;
    }


    /* Array operations: */

    case NEWARRAY:{
      pc++;
      ubyte s = P[pc];
      pc++;
      int n = val2int(c0v_pop(S));
      if(n < 0){
        c0_memory_error("Abort execution -> Invalid negative!");
      }
      c0_array* array = xcalloc(1, sizeof(c0_array));
      array->count = n;
      array->elt_size = s;
      array->elems = xcalloc(n,array->elt_size);
      c0v_push(S, ptr2val((void*)array));
      break;
    }

    case ARRAYLENGTH:{
      pc++;
      void* a = val2ptr(c0v_pop(S));
      c0_array* lenArray = (c0_array*)a;
      if(lenArray == NULL){
        c0_memory_error("Null memory error");
      }
      c0v_push(S, int2val(lenArray->count));
      break;
    }

    case AADDS:{
      pc++;
      int i = val2int(c0v_pop(S));
      void* array = val2ptr(c0v_pop(S));
      c0_array* a = (c0_array*)array;
      if(a == NULL){
        c0_memory_error("Null memory error");
      }
      int length = a->count;
      if(i < 0 || i >= length){
        c0_memory_error("Not a valid index");
      }
      char* arr = (char*)a->elems;
      c0v_push(S, ptr2val(&arr[a->elt_size*i]));
      break;
    }


    /* BONUS -- C1 operations */

    case CHECKTAG:

    case HASTAG:

    case ADDTAG:

    case ADDROF_STATIC:

    case ADDROF_NATIVE:

    case INVOKEDYNAMIC:

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}
