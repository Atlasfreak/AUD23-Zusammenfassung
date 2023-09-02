A = [3,5,1,7,2,8,2,9,0]
def insertionSort1(A):
    for i in range(1, len(A)):
        # insert A[i] in pre-sorted sequence A[0..i-1]
        key=A[i]
        j=i-1 # search for insertion point backwards
        while j>=0 and A[j]>key:
            A[j+1]=A[j] # move elements to right
            j=j-1
        A[j+1]=key
    return A

def insertionSort2(A):
    for i in range(1, len(A)):
        # insert A[i] in pre-sorted sequence A[0..i-1]
        key=A[i]
        j=i-1 # search for insertion point backwards
        while j>=0 and A[j]<key:
            A[j+1]=A[j] # move elements to right
            j=j-1
        A[j+1]=key
    return A

print(insertionSort1(A))
print(insertionSort2(A))

def partition(A, l, r):
    pivot=A[l];
    pl=l-1; pr=r+1
    while pl<pr:
        while True:
            pl=pl+1
            if A[pl]>= pivot:
                break
        while True:
            pr=pr-1
            if A[pr]<=pivot:
                break
        if pl<pr:
            temp = A[pl]
            A[pl] = A[pr]
            A[pr] = temp
        p=pr
    return (p, pr, pl, A)

print(partition([33,12,17,44,53,2], 0,5))