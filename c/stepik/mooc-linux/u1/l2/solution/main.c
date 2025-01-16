// solution for https://stepik.org/lesson/26303/step/8?unit=8181 in ./lib
#include <stdio.h>

int stringStat(const char *string, size_t multiplier, int *count);

int main() {
  char *s = "Vasya";
  int count = 13;
  int res = stringStat(s, 2, &count);
  if(res != 10) {
    printf("expected res 10 but was %d\n", res);
    return 1;
  } else if(count != 14) {
    printf("expected count 14 but was %d\n", count);
    return 2;
  } else {
    printf("OK\n");
    return 0;
  }
}
