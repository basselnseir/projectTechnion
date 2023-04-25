#!/usr/bin/env python
# coding: utf-8

# In[1]:


import pyrtl

def add_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        sum_wire = pyrtl.WireVector(wire_length) 
        sum_wire = wire1 + wire2
        sum_wire = sum_wire[0:wire_length]
        return sum_wire
      


# In[2]:


import pyrtl

def sub_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        sub_wire = pyrtl.WireVector(wire_length) 
        sub_wire = wire1 - wire2
        sub_wire = sub_wire[0:wire_length]
        return sub_wire
      


# In[3]:


import pyrtl

def neg_wire(wire):
    wire_length = wire.bitwidth
    neg_wire = pyrtl.WireVector(wire_length)
    zero_const = pyrtl.Const(0, bitwidth=wire_length)
    zero_wire = pyrtl.WireVecotr(wire_length)
    zero_wire |= zero_const
    neg_wire = zero_wire - wire
    neg_wire = neg_wire[0:wire_length]
    return neg_wire


# In[4]:


import pyrtl

def mul_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        mul_wire = pyrtl.WireVector(wire_length) 
        mul_wire = wire1 * wire2
        mul_wire = sub_wire[0:wire_length]
        return mul_wire
      


# In[5]:


import pyrtl

def and_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        and_wire = pyrtl.WireVector(wire_length) 
        and_wire = wire1 & wire2
        and_wire = sub_wire[0:wire_length]
        return and_wire
      


# In[6]:


import pyrtl

def or_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        or_wire = pyrtl.WireVector(wire_length) 
        or_wire = wire1 | wire2
        or_wire = sub_wire[0:wire_length]
        return or_wire


# In[7]:


import pyrtl

def not_reg(wire):
        wire_length = wire.bitwidth
        not_wire = pyrtl.WireVector(wire_length) 
        not_wire = ~wire
        return not_wire


# In[8]:


import pyrtl

def LT_regs(wire1,wire2):
    if(wire1.bitwidth != wire2.bitwidth):
        return
    else:
        wire_length = wire1.bitwidth
        LT_wire = pyrtl.WireVector(wire_length) 
        LT_wire = wire1 < wire2
        return LT_wire


# In[9]:


import pyrtl

def shiftLeft_wire(wire):
    wire_length = wire.bitwidth
    shifted_wire = pyrtl.WireVector(wire_length)
    shifted_Wire = pyrtl.concat(pyrtl.Const(0, bitwidth=1), wire)
    shifted_Wire = shifted_Wire[0:wire_length]
    return shifted_Wire


# In[10]:


import pyrtl

def shiftRight_wire(wire):
    wire_length = wire.bitwidth
    shifted_wire = pyrtl.WireVector(wire_length)
    shifted_Wire = pyrtl.concat(wire, pyrtl.Const(0, bitwidth=1))
    shifted_Wire = shifted_Wire[0:wire_length]
    return shifted_Wire


# In[11]:


from instruction_set import AOP

def AlU_function(reg1, reg2, op):
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
        result <<= LT_regs(wire1)
    return result
    
        


# In[ ]:





# In[ ]:




