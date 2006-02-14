/* This is PAPI_ipc in the examples directory */

#include <stdio.h>
#include <stdlib.h>
#include "papi.h"

main()
{ 
  float real_time, proc_time,ipc;
  long_long ins;
  float real_time_i, proc_time_i, ipc_i;
  long_long ins_i;
  int retval;

  if((retval=PAPI_ipc(&real_time_i,&proc_time_i,&ins_i,&ipc_i)) < PAPI_OK)
  { 
    printf("Could not initialise PAPI_ipc \n");
    printf("retval: %d\n", retval);
    exit(1);
  }

  my_slow_code();

  
  if((retval=PAPI_ipc( &real_time, &proc_time, &ins, &ipc))<PAPI_OK)
  {    
    printf("retval: %d\n", retval);
    exit(1);
  }


  printf("Real_time: %f Proc_time: %f Total instructions: %lld IPC: %f\n", 
         real_time, proc_time,ins,ipc);

  /* clean up */
  PAPI_shutdown();
  exit(0);
}

int my_slow_code()
{
    int i = 0;
    size_t size = 1 << 28;   /* get a nice chunk, bigger than cache */
    unsigned int* data = malloc(size * sizeof(unsigned int));
    unsigned int idx = 42;
    void* startB = &&start;
    void* endB   = &&end;
    
    start:
        if (i++ >= 100000) goto *endB;
        data[idx % size] = idx;
        idx = 70119 * (idx+data[idx % (size-912)]) + 343;
        goto *startB;
    end:
    
    free(data);
}
