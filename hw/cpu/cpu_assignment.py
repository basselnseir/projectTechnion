#!/usr/bin/env python
# coding: utf-8

# In[1]:


import sys
sys.path.append("../base")

import boilerplate
import alu_assignment

import pyrtl

from pyrtl import *

import z3
z3.set_param(proof=True)


# In[2]:


from instruction_set import *

reset_working_block()

pc = Register(name='pc', bitwidth=16)
sp = Register(name='sp', bitwidth=16)
r0 = Register(name='r0', bitwidth=16)
r1 = Register(name='r1', bitwidth=16)
mem = MemBlock(name='mem', bitwidth=16, addrwidth=32,
               max_read_ports=30)
rom = RomBlock(name='rom', bitwidth=16, addrwidth=16, romdata=[0b101011, 0b111011],
               pad_with_zeros=True)  # needed for C compilation
out = Output(name='out', bitwidth=4)


# In[3]:


def push(val):
    mem[sp] |= val
    sp.next |= sp + 1
    pc.next |= pc + 1


# In[4]:


def pop(cnt):
    with (sp > 0):
        with cnt == 1:
            r0.next |= mem[sp]
        with cnt == 2:
            r1.next |= mem[sp]
            r0.next |= mem[sp - 1]
    sp.next |= sp - cnt
    pc.next |= pc + 1


# In[5]:


def dup(ofs):
    with (ofs) > 0:
        val = mem[sp - ofs]
        push(val)


# In[6]:


from instruction_set import AOP
from alu_assignment import ALU_function


def alu(op):
    
    push(ALU_function(r0, r1, op))


# In[7]:


def load():
    push(mem[r0])


# In[8]:


def store():
    mem[r1] |= r0


# In[9]:


def jmp(addr):
    pc.next |= addr


# In[10]:


def jz(addr):
    zero_const = pyrtl.Const(0, bitwidth=16)
    with r0 == zero_const:
        jmp(addr)
    


# In[11]:


def jnz(addr):
    zero_const = pyrtl.Const(0, bitwidth=16)
    with r0 != zero_const:
        jmp(addr)
    


# In[12]:


def ret(flag):
    jmp(r0)
    with flag == 1:
        push(r1)


# In[13]:


import instruction_set

instr = rom[pc]
out <<= mem[sp]

op = instr[0:4]

with conditional_assignment:
    with (op == PUSH):
        val = instr[4:]
        push(val)
    with (op == POP):
        cnt = instr[4:]
        pop(cnt)
    with (op == DUP):
        ofs = instr[4:]
        dup(ofs)
    with (op == STOR):
        store()
    with (op == LOAD):
        load()
    with (op == JMP):
        addr = instr[4:]
        jmp(addr)
    with (op == JZ):
        addr = instr[4:]
        jz(addr)
    with (op == JNZ):
        addr = instr[4:]
        jnz(addr)
    with (op == RET):
        flag = instr[4:]
        jmp(flag)
    with (op == ALU):
        alu_op = instr[4:]
        alu(alu_op)
    
        


# In[14]:


d_sp = Output(name='d_sp', bitwidth=16)
d_pc = Output(name='d_pc', bitwidth=16)
d_r0 = Output(name='d_r0', bitwidth=16)
d_r1 = Output(name='d_r1', bitwidth=16)
d_instr = Output(name='d_instr', bitwidth=16)

d_sp <<= sp
d_pc <<= pc
d_r0 <<= r0
d_r1 <<= r1
d_instr <<= instr

# Debug the lowest 16 memory addresses
d_memaddrs = range(16)
reads = [mem[i] for i in d_memaddrs]
arr = Output(bitwidth=len(reads)*16, name="d_mem")
arr <<= concat_list(reads)


# In[15]:


vid_y = Output(name='vid_y', bitwidth=8)
vid_out = Output(name='vid_out', bitwidth=256)

vid_scan = Register(name='vid_scan', bitwidth=5)
vid_scan.next <<= vid_scan + 1
vid_y <<= 18 + vid_scan
vid_out <<= 0xff0f0ff0000


# In[16]:


import os
from simulate import CCompiledSimulation


# In[17]:


CCompiledSimulation(out_dir="obj")


# In[18]:


os.system("make")


# In[20]:


# If you don't have GNU make
if 0:
    os.system("gcc -O3 -Iobj -c obj/csim.c")
    os.system("g++ -pthread -Iobj --std=c++11 obj/csim.o simulate/csim_main.cpp -o bin/csim")


# In[21]:


os.environ['DEBUG_CPU'] = '1'
os.environ['DEBUG_MEM'] = '1'
os.environ['MAX_CYCLES'] = '20'
os.environ['OUT_DISPLAY'] = '0'
os.system('bin/csim');


# In[ ]:





# In[ ]:




