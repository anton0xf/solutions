#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <dlfcn.h>
#include <stdlib.h>

int main(int argc, char* argv[]) {
  if(argc != 4) {
    fprintf(stderr, "Usage: ./solution path function-name int-arg\n");
    return 1;
  }
  char *path = argv[1];
  char *func = argv[2];
  char *arg_str = argv[3];
  int arg = atoi(arg_str);

  void *hdl = dlopen(path, RTLD_LAZY);
  if (NULL == hdl) {
    fprintf(stderr, "%s\n", dlerror());
    return 2;
  }
  dlerror(); /* Clear any existing error */

  int (*shared)(int) = (int (*)(int)) dlsym(hdl, func);
  
  char *error = dlerror();
  if (error != NULL) {
    fprintf(stderr, "%s\n", error);
    return 3;
  }
  
  int res = shared(arg);
  printf("%d\n", res);
  
  dlclose(hdl);
  return 0;
}
