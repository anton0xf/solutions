#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <dlfcn.h>

void (*hello_message)(const char*);

void* init_library() {
  void *hdl = dlopen("./libhello.so", RTLD_LAZY);
  if (NULL == hdl) {
    fprintf(stderr, "%s\n", dlerror());
    return NULL;
  }
  dlerror();    /* Clear any existing error */

  hello_message = (void (*)(const char*)) dlsym(hdl, "hello_message");
  char *error = dlerror();
  if (error != NULL) {
    fprintf(stderr, "%s\n", error);
    return NULL;
  }

  return hdl;
}

int main() {
  void *hdl = init_library();
  if (NULL != hdl) {
    hello_message("Vasya");
  } else {
    printf("Library was not loaded\n");
  }
  dlclose(hdl);
  return 0;
}
