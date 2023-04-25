#!/usr/bin/env python
# coding: utf-8

# In[1]:


import sys
sys.path.append("../base")

import boilerplate
from pyrtl import *

import z3
z3.set_param(proof=True)


# In[2]:


import pyrtl

def add_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        sum_wire = pyrtl.WireVector(wire_length, 'sum_wire') 
        sum_wire <<= wire1 + wire2
        return sum_wire[0:wire_length]
      


# In[3]:


import pyrtl

def sub_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        sub_wire = pyrtl.WireVector(wire_length, 'sub_wire') 
        sub_wire <<= wire1 - wire2
        return sub_wire[0:wire_length]
      


# In[4]:


import pyrtl

def neg_wire(wire):
    wire_length = wire.bitwidth
    neg_wire = pyrtl.WireVector(wire_length, 'neg_wire')
    zero_const = pyrtl.Const(0, bitwidth=wire_length)
    zero_wire = pyrtl.WireVector(wire_length, 'zero_wire')
    zero_wire |= zero_const
    neg_wire <<= zero_wire - wire
    return neg_wire[0:wire_length]


# In[5]:


import pyrtl

def mul_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        mul_wire = pyrtl.WireVector(wire_length, 'mul_wire') 
        mul_wire <<= wire1 * wire2
        return mul_wire[0:wire_length]
      


# In[6]:


import pyrtl

def and_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        and_wire = pyrtl.WireVector(wire_length, 'and_wire') 
        and_wire <<= wire1 & wire2
        return and_wire[0:wire_length]
      


# In[7]:


import pyrtl

def or_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        or_wire = pyrtl.WireVector(wire_length, 'or_wire') 
        or_wire <<= wire1 | wire2
        return or_wire[0:wire_length]


# In[8]:


import pyrtl

def not_regs(wire):
        wire_length = wire.bitwidth
        not_wire = pyrtl.WireVector(wire_length, 'not_wire') 
        not_wire <<= ~wire
        return not_wire


# In[9]:


import pyrtl

def LT_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        LT_wire = pyrtl.WireVector(wire_length, 'LT_wire') 
        LT_wire <<= wire1 < wire2
        return LT_wire


# In[10]:


import pyrtl

def shiftRight_wire(wire):
    wire_length = wire.bitwidth
    shifted_wire = pyrtl.WireVector(wire_length, 'right_shifted_wire')
    shifted_wire <<= pyrtl.concat(pyrtl.Const(0, bitwidth=1), wire)
    return shifted_wire[1:wire_length+1]


# In[11]:


import pyrtl

def shiftLeft_wire(wire):
    wire_length = wire.bitwidth
    shifted_wire = pyrtl.WireVector(wire_length, 'left_shifted_wire')
    shifted_wire <<= pyrtl.concat(wire, pyrtl.Const(0, bitwidth=1))
    return shifted_wire[0:wire_length]


# In[12]:


from instruction_set import AOP

def ALU_function(reg1, reg2, op):
    wire1 = pyrtl.WireVector(reg1.bitwidth)
    wire2 = pyrtl.WireVector(reg2.bitwidth)
    wire1 <<= reg1
    wire2 <<= reg2
    result = pyrtl.WireVector(reg1.bitwidth)
    if(op == AOP.ADD):
        result <<= add_regs(wire1, wire2)
    elif(op == AOP.SUB):
        result <<= sub_regs(wire1, wire2)
    elif(op == AOP.MUL):
        result <<= mul_regs(wire1, wire2)
    elif(op == AOP.SHL):
        result <<= shiftLeft_wire(wire1)
    elif(op == AOP.SHR):
        result <<= shiftRight_wire(wire1)
    elif(op == AOP.NEG):
        result <<= neg_wire(wire1)
    elif(op == AOP.AND):
        result <<= and_regs(wire1, wire2)
    elif(op == AOP.OR):
        result <<= or_regs(wire1, wire2)
    elif(op == AOP.NOT):
        result <<= not_regs(wire1)
    elif(op == AOP.LT):
        result <<= LT_regs(wire1, wire2)
    return result
    
        


# In[13]:


register1 = pyrtl.Input(4, 'register1')
register2 = pyrtl.Input(4, 'register2')
result = pyrtl.Output(4, 'result')

result <<= ALU_function(register1, register2, 12)

sim = Simulation()
for i in range(10):
    sim.step({
        'register1': 4,
        'register2': 6
    
    })
sim.tracer.render_trace()
sim.tracer.print_trace()


# In[ ]:





# In[ ]:





# In[ ]:




