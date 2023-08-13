#!/usr/bin/env python
# coding: utf-8

# In[2]:


#import cpu_assignment
#from cpu_assignment import *
from instruction_set import *
import periph
from periph import gpio_adapter


# In[3]:


BOOTLOADER_BLOCKS = ['_loop',
                    (PUSH, 0xc000),
                    (POP, 1),
                    LOAD,
                    (PUSH, 0xffff),
                    (DUP, 1),
                    (POP, 2),
                    (ALU, AOP.SUB),
                    (POP, 1),
                    (JZ, '_end'),
                    (PUSH, 0Xc001),
                    (POP, 1),
                    LOAD,
                    (DUP, 0),
                    (PUSH, 0xc003),
                    (POP, 2),
                    STOR,
                     (DUP, 0),
                     (PUSH, 1),
                     (POP, 2),
                     (ALU, AOP.SUB),
                     (PUSH, 0x5400),
                     (POP, 2),
                     (ALU, AOP.ADD),
                     (PUSH, 2),
                     (POP, 2),
                     (ALU, AOP.MUL),
                     (DUP, 2),
                     (DUP, 1),
                     (POP, 2),
                     STOR,
                     (PUSH, 1),
                     (POP, 2),
                     (ALU, AOP.ADD),
                     (POP, 2),
                     STOR, 
                     (POP, 1),
                    (JMP, '_loop'),
                    '_end',
                     (POP, 1),
                     (PUSH, 0x5400),
                     (POP, 1),
                     (RET, 0)
                    ]       


# In[ ]:





# In[ ]:




