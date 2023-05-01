import time

def stuff(a,k,s):
    i = 0
    while i < len(a) :
        if a[i:i+len(k)] == k:
            # insert_ids.append(i+len(k))
            a.insert(i+len(k),s)
            i += len(k)
        else:
            i += 1
    return a

# 00111010111001
# print(stuff(a,k,s))

def destuff(a,k):
    i = 0
    # print("a : ",a)
    while i < len(a) :
        if a[i:i+len(k)] == k:
            if a[i+len(k)] != s :
                return -1
            else:
                del a[i+len(k)]
                # print("a : ",a)
                i += len(k)
        else:
            i += 1
    return a

# print("After destuff : ",destuff(stuff(a,k,s),k))

def add_flags(a,f):
    return f+a+f

def rem_flags(a,f):
    if a[:len(f)] == f and a[-(len(f)):] == f:
        return a[len(f):-(len(f))]
    else:
        return -1

# a = [True,False,True]
# f = [False,True]
# print("add_flag : ",add_flags(a,f))
# print("rem_flag : ", rem_flags(add_flags(a,f),f))

a = [False,False,True,True,True,False,True,False,True,True,True,False,False,True]
k = [True, True]
f = [False, True, True, True, False]
s = False

st = time.time()

for i in range(1000):
    b = stuff(a,k,s)
    b1 = add_flags(b,f)
    b2 = rem_flags(b1,f)
    b3 = destuff(b2,k)
    # remove modularity and do in one pass

et = time.time()

print(f"time taken = {et-st}")

