#!/usr/bin/env python
# coding: utf-8

# In[1]:


import boilerplate

import pyrtl
from pyrtl import *

import z3


# In[2]:


reset_working_block()
working_block()


# In[3]:


def halfAdder(a, b):
    sum1 = a^b
    carry1 = a&b
    to_return = [sum1, carry1]
    return to_return


# In[4]:


def fullAdder(a, b, c):
    result1 = halfAdder(a, b)
    sum1 = result1[0]
    carry1 = result1[1]
    result2 = halfAdder(sum1, c)
    sum2 = result2[0]
    carry2 = result2[1]
    to_return = [sum2, carry1 | carry2]
    return to_return


# In[5]:


import z3
from z3 import BitVec, BV2Int
from z3 import *

def addKbit(k):
    _r = [BitVec('r%i'%i, k) for i in range(2)]
    r = [[z3.Extract(i, i, b) for i in range(k)] for b in _r]
    out = BitVec('out', k + 1)
    tmp = halfAdder(r[0][0], r[1][0])
    carry1 = tmp[1]
    to_return = [tmp[0]]
    for i in range(1, k):
        tmp = fullAdder(r[0][i], r[1][i], carry1)
        to_return.insert(0, tmp[0])
        carry1 = tmp[1]   
    to_return.insert(0, carry1)
    tmp1 = z3.Concat(to_return[0], to_return[1])
    for i in range(2, len(to_return)):
        finalTmp = z3.Concat(tmp1, to_return[i]) 
        tmp1 = finalTmp
    s = z3.Solver()
    s.add(out == tmp1)
    res = s.check([z3.Not(BV2Int(_r[0]) + BV2Int(_r[1]) == BV2Int(out))])
    #res2 = s.model()
    print(res)
    #print(res2)


# In[6]:


import z3

def net_to_smt(wb):
    # we want to add the operation to the assertionList
    assertionList = []
    wiresList = {}
    index = 0
    for net in wb:
        if net.op =='^':
            dest = z3.BitVec(net.dests[0].name, net.dests[0].bitwidth)
            arg1 = z3.BitVec(net.args[0].name, net.args[0].bitwidth)
            arg2 = z3.BitVec(net.args[1].name, net.args[1].bitwidth)
            arg = arg1 ^ arg2
            expr = dest == arg
        elif net.op =='&':
            dest = z3.BitVec(net.dests[0].name, net.dests[0].bitwidth)
            arg1 = z3.BitVec(net.args[0].name, net.args[0].bitwidth)
            arg2 = z3.BitVec(net.args[1].name, net.args[1].bitwidth)
            arg = arg1 & arg2
            expr = dest == arg
        elif net.op =='|':
            dest = z3.BitVec(net.dests[0].name, net.dests[0].bitwidth)
            arg1 = z3.BitVec(net.args[0].name, net.args[0].bitwidth)
            arg2 = z3.BitVec(net.args[1].name, net.args[1].bitwidth)
            arg = arg1 | arg2
            expr = dest == arg              
        elif net.op == 's':
            dest = z3.BitVec(net.dests[0].name, net.dests[0].bitwidth)
            reg = z3.BitVec(net.args[0].name, net.args[0].bitwidth)
            wiresList[net.args[0].name] = reg
            arg = z3.Extract(net.op_param[0], net.op_param[0], reg)
            expr = dest == arg   
        elif net.op == 'c':
            dest = z3.BitVec(net.dests[0].name, net.dests[0].bitwidth)
            reg = z3.BitVec(net.args[0].name, net.args[0].bitwidth)
            arg = reg
            for i in range(1, len(net.args)):
                reg_i = z3.BitVec(net.args[i].name, net.args[i].bitwidth)
                reg = z3.Concat(reg, reg_i)
            expr = dest == reg
        elif net.op == 'w':
            dest = z3.BitVec(net.dests[0].name, net.dests[0].bitwidth)
            wiresList[net.dests[0].name] = dest
            arg = z3.BitVec(net.args[0].name, net.args[0].bitwidth)
            expr = dest == arg
        assertionList.append(expr)
    return wiresList, [], assertionList


# In[7]:


wb = working_block()

addKbit(1)


# In[8]:


wires, ops, assertions = net_to_smt(wb)

s = z3.Solver()
for phi in assertions:
    print(phi)
    s.add(phi)

