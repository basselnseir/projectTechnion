#!/usr/bin/env python
# coding: utf-8

# In[1]:


import parser
from parser import IRParser

from ir import Var, Const, Seq, If, FuncDef


# In[2]:


ret_loc_count = 0
end_count = 0 
else_count =0

def modify_global_else():
    global else_count
    else_count = else_count + 1

def modify_global_end():
    global end_count
    end_count = end_count + 1
    
def modify_global_ret():
    global ret_loc_count
    ret_loc_count = ret_loc_count + 1
    
    
def compilerFunc():
    p = IRParser()
   # with open(filename, 'r') as file:
    #    file_contents = file.read()
    
    
    pList = p('''
    fact(1) = 
          if 1 < $0 then fact ($0 - 1) * $0
          else 1
    ''')
    # p_list contains list of funcDef: [funcDef_1, funcDef_2, funcDef_3, ...., funcDef_n]
    to_return = []
    tmp_instr = []
    counter = 0
    to_return.append(('PUSH', 'finish'))
    # maybe we need to append ('JMP', 'main')
    for funcDef in pList:
        tmp_instr.append(funcDef.name)
        counter = funcDef.nargs
        tmp_instr, counter = compilerFunc_aux(funcDef.body, tmp_instr, counter)
        if tmp_instr == None:
            continue
        tmp_instr.append(('YANK', (1, counter - 2)))
        tmp_instr.append(('POP', 2))
        tmp_instr.append(('RET', 1))
        to_return = to_return + tmp_instr
        tmp_instr = []
    to_return.append('finish')
    to_return.append(('POP', 1))
    to_return.append(('HALT', 0))
    return to_return

def compilerFunc_aux(node, to_return, counter):
    
    if isinstance(node, Const):
        to_return.append(('PUSH', node[0]))
        counter = counter + 1
        return to_return, counter
            
    elif isinstance(node, Var):
        offs = counter - node[0] - 1
        to_return.append(('DUP', offs))
        counter = counter + 1
        return to_return, counter
            
            
    elif isinstance(node, If):
        cond = node[0]
        to_return, counter = compilerFunc_aux(cond, to_return, counter)
        to_return.append(('POP', 1))
        counter = counter - 1
        _else_loc = '_else_' + str(else_count)
        #else_count = else_count + 1
        modify_global_else()
        to_return.append(('JZ', _else_loc))
        then = node[1]
        to_return, counter = compilerFunc_aux(then, to_return, counter)
        _end_loc = '_end_' + str(end_count)
        #end_count = end_count + 1
        modify_global_end()
        to_return.append(('JMP', _end_loc))
        els = node[2]
        to_return.append(_else_loc)
        to_return, counter = compilerFunc_aux(els, to_return, counter)
        to_return.append(_end_loc)
        return to_return, counter
            
    elif isinstance(node, Seq):
        for e in node[0]:
            to_return, counter = compilerFunc_aux(e, to_return, counter)
        return to_return, counter
        
    else:
        if node[0] == '-':
            if len(node) == 2:
                to_return, counter = compilerFunc_aux(node[1], to_return, counter)
                to_return.append(('POP', 1))
                to_return.append(('ALU', 'NEG'))
                return to_return, counter
            
            elif len(node) == 3:
                to_return, counter = compilerFunc_aux(node[1], to_return, counter)
                to_return, counter = compilerFunc_aux(node[2], to_return, counter)
                to_return.append(('POP', 2))
                to_return.append(('ALU', 'SUB'))
                counter = counter - 1
                return to_return, counter
            
        elif node[0] == '~':
            to_return, counter = compilerFunc_aux(node[1], to_return, counter)
            to_return.append(('POP', 1))
            to_return.append(('ALU', 'NOT'))
            return to_return, counter
        
        elif node[0] == '*':
            to_return, counter = compilerFunc_aux(node[1], to_return, counter)
            to_return, counter = compilerFunc_aux(node[2], to_return, counter)
            to_return.append(('POP', 2))
            to_return.append(('ALU', 'MUL'))
            counter = counter - 1
            return to_return, counter
            
        elif node[0] == '+':
            to_return, counter = compilerFunc_aux(node[1], to_return, counter)
            to_return, counter = compilerFunc_aux(node[2], to_return, counter)
            to_return.append(('POP', 2))
            to_return.append(('ALU', 'ADD'))
            counter = counter - 1
            return to_return, counter
            
        elif node[0] == '<':
            to_return, counter = compilerFunc_aux(node[1], to_return, counter)
            to_return, counter = compilerFunc_aux(node[2], to_return, counter)
            to_return.append(('POP', 2))
            to_return.append(('ALU', 'LT'))
            counter = counter - 1
            return to_return, counter
        
        elif node[0] == '<<':
            to_return, counter = compilerFunc_aux(node[1], to_return, counter)
            to_return, counter = compilerFunc_aux(node[2], to_return, counter)
            to_return.append(('POP', 2))
            to_return.append(('ALU', 'SHL'))
            counter = counter - 1
            return to_return, counter
        
        elif node[0] == '>>':
            to_return, counter = compilerFunc_aux(node[1], to_return, counter)
            to_return, counter = compilerFunc_aux(node[2], to_return, counter)
            to_return.append(('POP', 2))
            to_return.append(('ALU', 'SHR'))
            counter = counter - 1
            return to_return, counter
        
        elif node[0] == '|':
            to_return, counter = compilerFunc_aux(node[1], to_return, counter)
            to_return, counter = compilerFunc_aux(node[2], to_return, counter)
            to_return.append(('POP', 2))
            to_return.append(('ALU', 'OR'))
            counter = counter - 1
            return to_return, counter
        
        elif node[0] == '&':
            to_return, counter = compilerFunc_aux(node[1], to_return, counter)
            to_return, counter = compilerFunc_aux(node[2], to_return, counter)
            to_return.append(('POP', 2))
            to_return.append(('ALU', 'AND'))
            counter = counter - 1
            return to_return, counter
        
        elif node[0] == 'ignore':
            return to_return, counter
            
        elif node[0] == '@' or node[0] == '@.':
            _ret_loc = '_ret_loc_' + str(ret_loc_count)
            #ret_loc_count = ret_loc_count + 1
            modify_global_ret()
            old_counter = counter
            to_return.append(('PUSH', _ret_loc))
            counter = counter + 1
            #for arg in node[2]:
            #    to_return, counter = compilerFunc_aux(arg, to_return, counter)
            if (len(node) > 2):
                to_return, new_counter = compilerFunc_aux(node[2], to_return, counter)
                counter = new_counter - counter 
            else: counter = 0
            to_return.append(('JMP', node[1]))
            to_return.append(_ret_loc)
            return_value = 1
            counter = old_counter + return_value
            return to_return, counter
        
            


# In[3]:


try1 = compilerFunc()
print(try1)

