#!/usr/bin/env python
# coding: utf-8

# In[1]:


import sys
sys.path.append("../base")

import boilerplate
import alu_assignment

import pyrtl
import ctypes

from pyrtl import *
from assembler import asm, disasm, disasm_pretty, asm_bin

import periph
from periph import gpio_adapter

import z3
z3.set_param(proof=True)


# In[2]:


from instruction_set import *
from test1 import BLOCKS
from Bootloader import BOOTLOADER_BLOCKS

reset_working_block()

romFile = asm(BOOTLOADER_BLOCKS, start_addr=0)  
ramFile = asm(BLOCKS, start_addr=0)
ramFile.save_bin('ramFile.bin')

with open("ramFile.bin", "rb") as file:
    data = file.read()
    for byte in data:
        bin_byte = bin(byte)
        print(bin(byte), end=' ')
binary_list = [bin(num)[2:] for num in ramFile.words]
#print(ramFile.words)
#print(binary_list)

pc = Register(name='pc', bitwidth=16)
sp = Register(name='sp', bitwidth=16)
r0 = Register(name='r0', bitwidth=16)
r1 = Register(name='r1', bitwidth=16)
mem = MemBlock(name='mem', bitwidth=16, addrwidth=32,
               max_read_ports=30, max_write_ports = 30, asynchronous=True)
rom = RomBlock(name='rom', bitwidth=20, addrwidth=20, romdata=romFile.words,
               pad_with_zeros=True)  # needed for C compilation
out = Output(name='out', bitwidth=4)


# In[3]:


def push(val):
    mem[sp] |= val
    sp.next |= sp + 1
    pc.next |= pc + 1


# In[4]:


def pop(cnt):
    with cnt == 1:
        with sp > 0:
            r0.next |= mem[sp - 1]
            sp.next |= sp - 1
            pc.next |= pc + 1
    with cnt == 2:
        with sp > 1:
            r1.next |= mem[sp - 1]
            r0.next |= mem[sp - 2]
            sp.next |= sp - 2
            pc.next |= pc + 1
    


# In[5]:


def dup(ofs):
    with (sp - ofs) > 0:
        val = mem[sp - ofs - 1]
        push(val)
   # with (sp - ofs) <= 0:
        # pc.next |= pc + 1


# In[6]:


from instruction_set import AOP
from alu_assignment import ALU_function


def alu(op):
    push(ALU_function(r0, r1, op))
    


# In[7]:


def load():
    tmp = mem[r0]
    push(tmp)


# In[8]:


def store():
    tmp = r0
    mem[r1] |= tmp
    pc.next |= pc + 1


# In[9]:


def jmp(addr):
    with pc > 0x4000:
        pc.next |= 0x5400 + addr
    with pyrtl.otherwise:
        pc.next |= addr
    


# In[10]:


def jz(addr):
    zero_const = pyrtl.Const(0, bitwidth=16)
    with r0 == zero_const:
        jmp(addr)
    with r0 != zero_const:
        pc.next |= pc + 1


# In[11]:


def jnz(addr):
    zero_const = pyrtl.Const(0, bitwidth=16)
    with r0 != zero_const:
        jmp(addr)
    with r0 == zero_const:
        pc.next |= pc + 1


# In[12]:


def ret(flag):
    with pc > 0x4000:
        pc.next |= 0x5400 + r0
    with pyrtl.otherwise:
        pc.next |= r0
    with flag == 1:
        mem[sp] |= r1
        sp.next |= sp + 1


# In[13]:


def yank(i, j, yankCheck):
    for counter in range(4):
        mem[sp - i - j + counter] <<= MemBlock.EnabledWrite(mem[sp - i + counter], enable=yankCheck)
    sp.next |= sp - j
    pc.next |= pc + 1


# In[14]:


import instruction_set

instr = pyrtl.WireVector(name='instr', bitwidth=20)

with conditional_assignment:
    with pc > 0x4000:
        instr |= mem[2*pc]
    with pyrtl.otherwise:
        instr |= rom[pc]

out <<= mem[sp]

op = instr[0:4]
def CPU_Function():
    with conditional_assignment:
        with (op == PUSH):
            val = instr[4:20]
            push(val)
        with (op == POP):
            cnt = instr[4:20]
            pop(cnt)
        with (op == DUP):
            ofs = instr[4:20]
            dup(ofs)
        with (op == STOR):
            store()
        with (op == LOAD):
            load()
        with (op == JMP):
            addr = instr[4:20]
            jmp(addr)
        with (op == JZ):
            addr = instr[4:20]
            jz(addr)
        with (op == JNZ):
            addr = instr[4:20]
            jnz(addr)
        with (op == RET):
            flag = instr[4:20]
            ret(flag)
        with (op == ALU):
            alu_op = instr[4:20]
            alu(alu_op)
        with (op == YANK):
            index1 = instr[4:8]
            index2 = instr[8:20]
            yank(index1, index2, op == YANK)
    
        


# In[15]:


CPU_Function()
gpio_adapter(mem, 0xc000)


# In[16]:


d_sp = Output(name='d_sp', bitwidth=16)
d_pc = Output(name='d_pc', bitwidth=16)
d_r0 = Output(name='d_r0', bitwidth=16)
d_r1 = Output(name='d_r1', bitwidth=16)
d_instr = Output(name='d_instr', bitwidth=20)


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


# In[17]:


vid_y = Output(name='vid_y', bitwidth=8)
vid_out = Output(name='vid_out', bitwidth=256)

vid_scan = Register(name='vid_scan', bitwidth=5)
vid_scan.next <<= vid_scan + 1
vid_y <<= 18 + vid_scan
vid_out <<= 0xff0f0ff0000


# In[18]:


import os
from simulate import CCompiledSimulation


# In[19]:


CCompiledSimulation(out_dir="obj")


# In[20]:


os.system("make")


# In[21]:


# If you don't have GNU make
if 0:
    os.system("gcc -O3 -Iobj -c obj/csim.c")
    os.system("g++ -pthread -Iobj --std=c++11 obj/csim.o simulate/csim_main.cpp -o bin/csim")


# In[22]:


os.environ['DEBUG_CPU'] = '1'
os.environ['DEBUG_MEM'] = '1'
os.environ['MAX_CYCLES'] = '10000'
os.environ['OUT_DISPLAY'] = '0'
arguments = ['bin/csim', 'ramFile.bin']
arguments_str = " ".join(arguments)
os.system(arguments_str)


# In[ ]:





# In[ ]:




