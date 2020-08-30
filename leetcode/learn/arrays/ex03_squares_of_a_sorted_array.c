#include <stdlib.h>
#include <stdio.h>

inline int firstNonNegativeIndex(int* A, int ASize);
inline int square(int n);

/**
 * Note: The returned array must be malloced, assume caller calls free().
 */
int* sortedSquares(int* A, int ASize, int* returnSize){
    *returnSize = ASize;
    int* res = (int*)malloc(sizeof(int)*ASize);
    int i = firstNonNegativeIndex(A, ASize);
    int j = i;
    int k = 0; // res insert index
    while (j > 0 || i < ASize) {
        if (j == 0 || (i < ASize && A[i] < -A[j-1])) {
            res[k++] = square(A[i++]);
        } else {
            res[k++] = square(A[--j]);
        }
    }
    return res;
}

int main() {
    int A[] = {-4, -1, 0, 3, 10};
    int returnSize = 0;
    int size = sizeof(A)/sizeof(int);
    int* res = sortedSquares(A, size, &returnSize);
    printf("result: [");
    for(int i = 0; i < returnSize; i++) {
        printf("%d, ", res[i]);
    }
    printf("]\n");
    free(res);
}

int firstNonNegativeIndex(int* A, int ASize) {
    for (int i = 0; i < ASize; i++) {
        if (A[i] >= 0) {
            return i;
        }
    }
    return ASize;
}

int square(int n) {
    return n * n;
}
