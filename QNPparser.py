#!/usr/bin/env python 
# -*- coding:UTF-8 -*-
# 
"""
the qnp parser return a dict with hig level language described problem actioon set.
"""
import re
import os

class qnp_action:
    def __init__(self,actionnameline,prelist,efflist,all_variables,all_fluents) -> None:
        self.name = actionnameline
        self.prestate = {}
        self.effstate = {}
        for index in range(1,len(prelist)-1,2):
            if prelist[index+1] == '1':
                if prelist[index] in all_variables:
                    self.prestate[prelist[index]] = '>0' # '1' means '>0'
                elif prelist[index] in all_fluents:
                    self.prestate[prelist[index]] = 'True' # '1' means 'True'
                else:
                    print("format Error! Only 0/1 is allowed.")
                    raise Exception
            elif prelist[index+1] == '0':
                if prelist[index] in all_variables:
                    self.prestate[prelist[index]] = '=0' # '0' means '==0'
                elif prelist[index] in all_fluents:
                    self.prestate[prelist[index]] = 'False' # '0' means 'False'
                else:
                    print("format Error! Only 0/1 is allowed.")
                    raise Exception
        for index in range(1,len(efflist)-1,2):
            if efflist[index+1] == '1':
                if efflist[index] in all_variables:
                    self.effstate[efflist[index]] = 'Inc' # '1' means 'increase'
                elif efflist[index] in all_fluents:
                    self.effstate[efflist[index]] = 'True' # '1' means 'True'
                else:
                    print("format Error! Only 0/1 is allowed.")
                    raise Exception
            elif efflist[index+1] == '0':
                if efflist[index] in all_variables:
                    self.effstate[efflist[index]] = 'Dec' # '0' means 'decrease'
                elif efflist[index] in all_fluents:
                    self.effstate[efflist[index]] = 'False' # '0' means 'False'
                else:
                    print("format Error! Only 0/1 is allowed.")
                    raise Exception        
    
class QNP_Parser:
    def __init__(self,qnpfile) -> None:
        self.name = ""
        self.initstate = {}
        self.goalstate = {}
        self.stateRepresentation_variables = []
        self.stateRepresentation_fluents   = []
        self.actionscount = 0
        self.actionlist = [] # a1,a2,a3,...
        openqnpfile = open(qnpfile,'r',encoding='UTF-8')
        lines = [line for line in openqnpfile.readlines() if line.strip()]
        openqnpfile.close()
        linenumber = 0
        for line in lines:
            line = line.strip()
            linelist = re.split(r"[ ]+", line)
            #print(line)
            if linenumber == 0:
                self.name = linelist[0]
            elif linenumber == 1:
                for index in range(1,len(linelist)-1,2):
                    if linelist[index+1] == '1':
                        self.stateRepresentation_variables.append(linelist[index])# variables
                    elif linelist[index+1] == '0':
                        self.stateRepresentation_fluents.append(linelist[index])# fluents
                    else:
                        print("format Error! Only 0/1 is allowed.")
                        raise Exception
            elif linenumber == 2:
                for index in range(1,len(linelist)-1,2):
                    if linelist[index+1] == '1':
                        if linelist[index] in self.stateRepresentation_variables:
                            self.initstate[linelist[index]] = '>0' # '1' means '>0'
                        elif linelist[index] in self.stateRepresentation_fluents:
                            self.initstate[linelist[index]] = 'True' # '1' means 'True'
                        else:
                            print("format Error! Only 0/1 is allowed.")
                            raise Exception
                    elif linelist[index+1] == '0':
                        if linelist[index] in self.stateRepresentation_variables:
                            self.initstate[linelist[index]] = '=0' # '1' means '==0'
                        elif linelist[index] in self.stateRepresentation_fluents:
                            self.initstate[linelist[index]] = 'False' # '1' means 'False'
                        else:
                            print("format Error! Only 0/1 is allowed.")
                            raise Exception
                    else:
                        print("format Error! Only 0/1 is allowed.")
                        raise Exception
            elif linenumber == 3:
                for index in range(1,len(linelist)-1,2):
                    if linelist[index+1] == '1':
                        if linelist[index] in self.stateRepresentation_variables:
                            self.goalstate[linelist[index]] = '>0' # '1' means '>0'
                        elif linelist[index] in self.stateRepresentation_fluents:
                            self.goalstate[linelist[index]] = 'True' # '1' means 'True'
                        else:
                            print("format Error! Only 0/1 is allowed.")
                            raise Exception
                    elif linelist[index+1] == '0':
                        if linelist[index] in self.stateRepresentation_variables:
                            self.goalstate[linelist[index]] = '=0' # '1' means '==0'
                        elif linelist[index] in self.stateRepresentation_fluents:
                            self.goalstate[linelist[index]] = 'False' # '1' means 'False'
                        else:
                            print("format Error! Only 0/1 is allowed.")
                            raise Exception
                    else:
                        print("format Error! Only 0/1 is allowed.")
                        raise Exception 
            elif linenumber == 4:
                self.actionscount = int(line)   
            else: # linenumber == 5,8,11,14,...
                if linenumber+2 > len(lines)-1:
                    break
                self.actionlist.append(
                    qnp_action(
                        lines[linenumber].strip(),
                        re.split(r"[ ]+", lines[linenumber + 1].strip()),
                        re.split(r"[ ]+", lines[linenumber + 2].strip()),
                        self.stateRepresentation_variables,
                        self.stateRepresentation_fluents))
                linenumber = linenumber + 2
            linenumber = linenumber + 1            
                 

def main():
    """
    qnp parser
    """
    domainname = "gripper" # config domain here
    domainname = "blocks_clear"
    qnpfile = "examples/{0}/{0}.qnp".format(domainname)
    qnp_parser = QNP_Parser(qnpfile)
    print(qnp_parser.name)
    print(qnp_parser.initstate)
    print(qnp_parser.goalstate)
    print(qnp_parser.stateRepresentation_variables)#  
    print(qnp_parser.stateRepresentation_fluents)  #    
    print(qnp_parser.actionscount)
    for eachaction in qnp_parser.actionlist:
        print(eachaction.name)
        print(eachaction.prestate)
        print(eachaction.effstate)

if __name__ == '__main__':
    main()


































