
action_args_declear_andlist_dict_define_in_GologTree_Nests_assgined_in_main_regression = {} 
# init dict : 'hig_name(=xxx)' -> {'arg_1':'BlockType';'arg_6':'BlockType';......}
def add_global_args_declear_andlist_dict(key,value): # called by Nested_list2FOLExp().run_s Nested_list2FOLExpressionwithSituation function:
    global action_args_declear_andlist_dict_define_in_GologTree_Nests_assgined_in_main_regression
    action_args_declear_andlist_dict_define_in_GologTree_Nests_assgined_in_main_regression[key] = value # ，
    
import copy
class ActionMapGolog :
    def __init__(self,actionMaplist:list()) -> None:
        self.act_map_golog_dict = dict()
        GologTreeObj = GologExprTree()
        cplist = copy.deepcopy(actionMaplist)
        thegologprogramnodeTree = GologTreeObj.recursive_build_golog_tree(cplist[1]) # build the golog tree for mapping low golog program
        GologTreeObj.loop_set_s_i_s_o(thegologprogramnodeTree) # set the golog tree nodes's: 's_i' & 's_o'
        self.act_map_golog_dict[cplist[0][0]] = thegologprogramnodeTree

    def __str__(self) -> str:
        return str(self.act_map_golog_dict)
    

class Nested_list2FOLExp:
    def __init__(self):
        self.FOL_Exp = ""
        self.const_declare_in_andlist = {}# andlistrefinementMaparg_3 

    def insertConsForSort(self,OneOfUntyped_variableslist,curtype):
        """add to self.ConsForSort if not added before"""
        if OneOfUntyped_variableslist not in self.const_declare_in_andlist:
                    self.const_declare_in_andlist[OneOfUntyped_variableslist] = curtype
        else:
            if self.const_declare_in_andlist[OneOfUntyped_variableslist] == curtype:
                pass # already added before,just pass
            else:
                raise Exception(OneOfUntyped_variableslist +' is already defined as ' \
                                + self.const_declare_in_andlist[OneOfUntyped_variableslist] \
                                + '.For theorem prove,it can not defined again with another sort:' + curtype)
    # @staticmethod
    def run(self, group):
        self.Nested_list2FOLExpression(group)
        if self.FOL_Exp[-1] == ',':
            self.FOL_Exp = self.FOL_Exp[:-1] # clear(A),
        return self.FOL_Exp

    def Nested_list2FOLExpression(self, group):
        """self.Nested_list2FOLExpression"""
        while group:
            cur = group.pop(0)
            if type(cur) == type(list()):
                self.Nested_list2FOLExpression(cur)  # nested list
            elif type(cur) == type(str()):
                if cur == 'and' or cur == 'And':
                    if len(group) == 1:
                        self.Nested_list2FOLExpression(group)
                    else:  # >1,"and(1,2,...)""
                        self.FOL_Exp += 'And('
                        self.Nested_list2FOLExpression(group)
                        if self.FOL_Exp[-1] == ',':
                            self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                        self.FOL_Exp += ')'
                elif cur == 'Not' or cur == 'not':
                    if len(group) == 1:# ['Not',above[...]]
                        self.FOL_Exp += 'Not('
                        self.Nested_list2FOLExpression(group)
                        if self.FOL_Exp[-1] == ',':
                            self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                        self.FOL_Exp += '),'# And（Not(B==arg_3)Not(A==arg_4)）
                    else:
                        raise Exception("\'Not\' only accept one args.")
                elif cur == 'or' or cur == 'Or':
                    if len(group) == 1:
                        self.Nested_list2FOLExpression(group)
                    else:  # >1,"or(1,2,...)""
                        self.FOL_Exp += 'Or('
                        self.Nested_list2FOLExpression(group)
                        if self.FOL_Exp[-1] == ',':
                            self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                        self.FOL_Exp += '),'
                elif cur == 'exists' or cur == 'Exists':
                    cp_arg_declare_list = copy.deepcopy(group[0])
                    while cp_arg_declare_list !=[]:
                        cur_char_variables = cp_arg_declare_list.pop(0)# pop
                        if cur_char_variables[0] == '?' and '-' in cp_arg_declare_list:
                            index_of_sort_declare = 1 + cp_arg_declare_list.index('-')	# （） ，+1
                            self.insertConsForSort(cur_char_variables,cp_arg_declare_list[index_of_sort_declare])
                            #  andlist   self.const_declare_in_andlist 
                    #
                    self.FOL_Exp += 'Exists(['
                    for each in group[0]:
                        if each[0] == '?':
                            self.FOL_Exp += each[1:]
                            self.FOL_Exp += ','
                    self.FOL_Exp = self.FOL_Exp[:-1] # "[x,y,"" ==> "[x,y" 
                    self.FOL_Exp += '],' # [x,y],
                    self.FOL_Exp += '('  # [x,y],(
                    group.pop(0)
                    self.Nested_list2FOLExpression(group[0])
                    if self.FOL_Exp[-1] == ',':
                        self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                    self.FOL_Exp += ')'# '[x,y],('  ')'
                    self.FOL_Exp += '),'# 'Exists(['  ')'And()'('','
                elif cur == 'forall' or cur == 'ForAll' or cur == 'Forall':
                    self.FOL_Exp += 'ForAll(['
                    for each in group[0]:
                        if each[0] == '?':
                            self.FOL_Exp += each[1:]
                            self.FOL_Exp += ','
                    #
                    cp_arg_declare_list = copy.deepcopy(group[0])
                    while cp_arg_declare_list !=[]:
                        cur_char_variables = cp_arg_declare_list.pop(0)# pop
                        if cur_char_variables[0] == '?' and '-' in cp_arg_declare_list:
                            index_of_sort_declare = 1 + cp_arg_declare_list.index('-')	# （） ，+1
                            self.insertConsForSort(cur_char_variables,cp_arg_declare_list[index_of_sort_declare])
                            # andlist  self.const_declare_in_andlist 
                    self.FOL_Exp = self.FOL_Exp[:-1]
                    self.FOL_Exp += '],'
                    self.FOL_Exp += '('# 'ForAll([x,y],(' 
                    group.pop(0)  # ['?x','-','BlockType']
                    self.Nested_list2FOLExpression(group[0])
                    if self.FOL_Exp[-1] == ',':
                        self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','                    
                    self.FOL_Exp += ')'# 'ForAll([x,y],('  ')'
                    self.FOL_Exp += '),'# 'Exists(['  ')'And()
                elif cur == '==':
                    if (type(group[0]) == type(group[1])) and (type(group[0]) == type(str())):
                        self.FOL_Exp += (group[0].strip('?') + '==' + group[1].strip('?') + ',')
                        group.pop(0)
                    else:
                        raise Exception('Error usage of \' == \'.')
                    break
                elif cur == '!=':
                    if (type(group[0]) == type(group[1])) and (type(group[0]) == type(str())):
                        self.FOL_Exp += '('+ (group[0].strip('?') + '!=' + group[1].strip('?') + ','+s_i+'),')
                        group.pop(0)
                    else:
                        raise Exception('Error usage of \' != \'.')
                    break
                else:  # Predicates defined by users like "clear A"
                    
                    self.FOL_Exp += cur + '('
                    if len(group) != 0:
                        for each in group:
                            self.FOL_Exp += each.strip('?') + ','
                        group.clear() # above ['x','A'] --> []
                        self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                        self.FOL_Exp += '),'
                    else:  # zero arg predicate like"arm-empty""
                        self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                        self.FOL_Exp += ','
                    break
            else:
                raise Exception('Error Input format!')


    def run_s(self, group,s_i,s_o):
        self.Nested_list2FOLExpressionwithSituation(group,s_i,s_o)
        if self.FOL_Exp[-1] == ',':
            self.FOL_Exp = self.FOL_Exp[:-1] # 'clear(A,s_i),'-->'clear(A,s_i)'
        return self.FOL_Exp,self.const_declare_in_andlist# ?arg_6GologTest

    def Nested_list2FOLExpressionwithSituation(self, group,s_i,s_o):
        """self.Nested_list2FOLExpressionwithSituation's_o'，'s_i'"""
        while group:
            cur = group.pop(0)
            if type(cur) == type(list()):
                self.Nested_list2FOLExpressionwithSituation(cur,s_i,s_o)  # nested list
            elif type(cur) == type(str()):
                if cur == 'and' or cur == 'And':
                    if len(group) == 1:
                        self.Nested_list2FOLExpressionwithSituation(group,s_i,s_o)
                    else:  # >1,"and(1,2,...)""
                        self.FOL_Exp += 'And('
                        self.Nested_list2FOLExpressionwithSituation(group,s_i,s_o)
                        if self.FOL_Exp[-1] == ',':
                            self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                        self.FOL_Exp += ')'
                elif cur == 'Not' or cur == 'not':
                    if len(group) == 1:# ['Not',above[...]]
                        self.FOL_Exp += 'Not('
                        self.Nested_list2FOLExpressionwithSituation(group,s_i,s_o)
                        if self.FOL_Exp[-1] == ',':
                            self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                        self.FOL_Exp += '),'
                    else:
                        raise Exception("\'Not\' only accept one args.")
                elif cur == 'or' or cur == 'Or':
                    if len(group) == 1:
                        self.Nested_list2FOLExpressionwithSituation(group,s_i,s_o)
                    else:  # >1,"or(1,2,...)""
                        self.FOL_Exp += 'Or('
                        self.Nested_list2FOLExpressionwithSituation(group,s_i,s_o)
                        if self.FOL_Exp[-1] == ',':
                            self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                        self.FOL_Exp += '),'
                elif cur == 'exists' or cur == 'Exists':
                    exist_args_list = []
                    exist_args_dict = {} # GologTest
                    cp_group_var_sort = copy.deepcopy(group[0])
                    while(cp_group_var_sort):
                        cur = cp_group_var_sort.pop(0)
                        # if cur == '?arg_6':
                        #     print()
                        if cur[0] == '?':
                            exist_args_list.append(cur)
                        if cur == '-':
                            cur_sort =  cp_group_var_sort.pop(0)
                            for each_arg in exist_args_list:
                                exist_args_dict[each_arg]= cur_sort
                                add_global_args_declear_andlist_dict(each_arg,cur_sort) #   action_args_declear_andlist_dict_define_in_GologTree_Nests_assgined_in_main_regression main.py
                            exist_args_list = [] # ?x - Ball,?y - gripper
                    self.const_declare_in_andlist.update(exist_args_dict) # 
                    # cp_arg_declare_list = copy.deepcopy(group[0])
                    #     while cp_arg_declare_list !=[]:
                    #         cur_char_variables = cp_arg_declare_list.pop(0)# pop
                    #         if cur_char_variables[0] == '?' and '-' in cp_arg_declare_list:
                    #             index_of_sort_declare = 1 + cp_arg_declare_list.index('-')	# （） ，+1
                    #             self.insertConsForSort(cur_char_variables,cp_arg_declare_list[index_of_sort_declare])
                    #             # andlist  self.const_declare_in_andlist 
                    #
                    self.FOL_Exp += 'Exists(['
                    for each in group[0]:
                        if each[0] == '?':
                            self.FOL_Exp += each[1:]
                            self.FOL_Exp += ','
                    self.FOL_Exp = self.FOL_Exp[:-1] # "[x,y,"" ==> "[x,y" 
                    self.FOL_Exp += '],' # [x,y],
                    self.FOL_Exp += '('  # [x,y],(
                    group.pop(0)
                    self.Nested_list2FOLExpressionwithSituation(group[0],s_i,s_o)
                    if self.FOL_Exp[-1] == ',':
                        self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                    self.FOL_Exp += ')'# '[x,y],('  ')'
                    self.FOL_Exp += '),'# 'Exists(['  ')'And()'('','
                elif cur == 'forall' or cur == 'ForAll' or cur == 'Forall':
                    univer_args_list = []
                    univer_args_dict = {} # GologTest
                    cp_group_var_sort = copy.deepcopy(group[0])
                    while(cp_group_var_sort):
                        cur = cp_group_var_sort.pop(0)
                        if cur[0] == '?':
                            univer_args_list.append(cur)
                        if cur == '-':
                            cur_sort =  cp_group_var_sort.pop(0)
                            for each_arg in univer_args_list:
                                univer_args_dict[each_arg]= cur_sort
                                add_global_args_declear_andlist_dict(each_arg,cur_sort) #   action_args_declear_andlist_dict_define_in_GologTree_Nests_assgined_in_main_regression main.py
                            univer_args_list = [] # ?x - Ball,?y - gripper
                    self.const_declare_in_andlist.update(univer_args_dict) # 
                    # 
                    self.FOL_Exp += 'ForAll(['
                    for each in group[0]:
                        if each[0] == '?':
                            self.FOL_Exp += each[1:]
                            self.FOL_Exp += ','
                    self.FOL_Exp = self.FOL_Exp[:-1]
                    self.FOL_Exp += '],'
                    self.FOL_Exp += '('# 'ForAll([x,y],(' 
                    group.pop(0)  # ['?x','-','BlockType']
                    self.Nested_list2FOLExpressionwithSituation(group[0],s_i,s_o)
                    if self.FOL_Exp[-1] == ',':
                        self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','                    
                    self.FOL_Exp += ')'# 'ForAll([x,y],('  ')'
                    self.FOL_Exp += '),'# 'Exists(['  ')'And()
                elif cur == '==':
                    if (type(group[0]) == type(group[1])) and (type(group[0]) == type(str())):
                        self.FOL_Exp += '('+ (group[0].strip('?') + '==' + group[1].strip('?') + ','+s_i+'),')
                        group.pop(0)
                    else:
                        raise Exception('Error usage of \' == \'.')
                    break
                elif cur == '!=':
                    if (type(group[0]) == type(group[1])) and (type(group[0]) == type(str())):
                        self.FOL_Exp += '('+ (group[0].strip('?') + '!=' + group[1].strip('?') + ','+s_i+'),')
                        group.pop(0)
                    else:
                        raise Exception('Error usage of \' != \'.')
                    break
                else:  # Predicates defined by users like "clear A"
                    
                    self.FOL_Exp += cur + '('
                    if len(group) != 0:
                        for each in group:
                            self.FOL_Exp += each.strip('?') + ','
                        group.clear() # above ['x','A'] --> []
                        self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                        self.FOL_Exp += ','+s_i+'),'
                    else:  # zero arg predicate like"arm-empty""
                        self.FOL_Exp = self.FOL_Exp[:-1]  # del last ','
                        self.FOL_Exp += '('+s_i+'),'
                    break
            else:
                raise Exception('Error Input format!')


class GologNode:
    def __init__(self,temptype,gologlist) -> None:
        self.type = str()
        if temptype in [':GologTest',':GologSeq',':GologOr',':GologPicksExists',':GologIfThen',':GologIfElse','and']:
            self.type = temptype
        else:
            self.type = ':GologActTerm' 
            temp = gologlist[0].pop(0)
            self.ActionName = temp
        self.args = gologlist[0]
        self.situation_action_args = [] # [situation action args]
        self.set_of_s_io = set() # # set of tuple (s_i,s_o) for every nodes.built this only for the top node in classgologTree/loop_set_s_i_s_o
        
        self.const_declare_in_andlist = {} #   ？arg_6,Nested_list3FOLExp().run_s
        # (situation input) --> (situation output)
        # Poss(s_i) == \phi(s_i)
        # SSA:F(\vec{x},s_output) == \Psi_F(\vec{x},\delta,s_input)
        self.s_i = '' # situation input 
        self.s_o = '' # situation output
        self.s_act = set() # set of tuple (situation,action) 
        # self.total_pos_pre = []
        # self.total_neg_pre = []
        # self.total_pos_eff = []
        # self.total_neg_eff = []
        switch  = {
            ':GologActTerm' : self.GologActTerm,
            'and':          self.LogicAnd_InGolog,
            ':GologTest'  : self.GologTest   ,    
            ':GologIfThen'  : self.GologIfThen     ,  
            ':GologIfElse'  :  self.GologIfElse     , 
            ':GologSeq'  :  self.GologSeq    , 
            ':GologOr' :  self.GologOr       ,
            ':GologPicksExists' : self.GologPicksExists
        }
        switch[self.type](gologlist)

    #   ::= :GologActTerm
    def GologActTerm(self,gologlist):
        self.Actionargs = []
        for each in gologlist[0]:# [['?arg_1', 'A', '?arg_2']]
            if each[0] == '?':
                self.Actionargs.append(each[1:])        #?arg_1,A,?arg_2... 
            else:
                self.Actionargs.append(each)# Exist- blockType，


    #   ::= :GologTest 
    def GologTest(self,cnf_in_Golog_list):    
        self.andlist = cnf_in_Golog_list
        self.neg_andlist = []
        self.pos_andlist = []
        for each in self.andlist:
            if each[0] == "not":
                self.neg_andlist.append(each)
            else:
                self.pos_andlist.append(each)  # 

    #   ::= and
    def LogicAnd_InGolog(self,cnf_in_Golog_list):
        self.andlist = cnf_in_Golog_list 
        self.neg_andlist = []
        self.pos_andlist = []
        for each in self.andlist:
            if each[0] == "not":
                self.neg_andlist.append(each)
            else:
                self.pos_andlist.append(each) # 

    #   ::= :GologIfThen 
    def GologIfThen(self,gologlist):
        self.cond = gologlist[0]
        self.thenlist = gologlist[1]  # Golog-，GologExpr，，AST      

    #   ::= :GologIfElse 
    def GologIfElse(self,gologlist):
        self.cond = self.LogicAnd_InGolog (gologlist[0])
        # self.ifTrue = GologActTerm(Gologlist[1]) # recursively,it also could be GologExpr,it can be GologAction at most times.
        # self.elseFalse = GologActTerm(Gologlist[2])
        self.ifTrue = gologlist[1] # Golog- 
        self.elseFalse = gologlist[2] # Golog- 

    #   ::= :GologSeq       
    def GologSeq(self,gologlist):
        self.GologSeqNodes = [] # 
        # for each in Gologlist :
        #      self.GologProgramsSeq.append(GologActTerm(each)) # Seq，
        self.GologSeqlist = gologlist # [delta_1,delta_2,...,delta_n] ,list
        # self.GologSeqNodes_init = None # [delta_1,delta_2,delta_3,...] ==> [':GologSeq', [':GologSeq',delta_1,delta_2,], delta_3]
        # self.GologSeqNodes_tail = None # Seq[Golog1,Golog2,...]
        
    #   ::= :GologOr        
    def GologOr(self,gologlist):
        self.GologOrNodes = [] # 
        self.GologOrlist = gologlist # Golog-   Or[Golog1,Golog2,...]

    #   ::= :GologPicksExists
    def GologPicksExists(self,gologlist):
        self.PickVars = []
        for each in gologlist[0]:
            if each[0] == '?':
                self.PickVars.append(each[1:])
        self.ExistsFormula = gologlist[1] # Golog-,

    def dump_golog_tree_pre(self) -> str:
        formula = ""
        def list_args2str(argslist):
            args2str = '['
            for each in argslist:
                args2str+=each+','
            if args2str[-1] == ',':
                args2str = args2str[:-1]
            args2str+='],'
            return args2str
        def actionlist2str(ActionName,actiontermlist,s_i):
            actiontermlist_str = 'Poss('+ActionName + '('
            if len(actiontermlist) >= 1:# ，
                for each in actiontermlist:
                    if each[0] == '?':
                        actiontermlist_str += each[1:] + ',' # ?x ?y
                    else:
                        actiontermlist_str += each + ',' # A,B,LEFT,RIGHT
                if actiontermlist_str[-1] == ',':# 
                    actiontermlist_str = actiontermlist_str[:-1]
            actiontermlist_str += '),'+ s_i +')'# 
            return actiontermlist_str
        if self.type ==':GologActTerm':
            formula += ''  + actionlist2str(self.ActionName,self.Actionargs,self.s_i) 
        elif self.type == 'and':
            # print(str(self.andlist[0]))
            andlist_str,returned_const_declare_in_andlist = Nested_list2FOLExp().run_s(copy.deepcopy(self.andlist[0]),self.s_i,self.s_o)
            # if '?arg_1' in returned_const_declare_in_andlist.keys():
            #     print()
            self.const_declare_in_andlist.update(returned_const_declare_in_andlist)
            # andlist_str = str(self.andlist)
            formula += ''+ andlist_str 
        elif self.type == ':GologTest':
            # print(str(self.andlist[0])) #['and', ['holding', '?x'], ['not', ['above', '?x', 'A']], ['clear', '?y']]
            andlist_str,returned_const_declare_in_andlist = Nested_list2FOLExp().run_s(copy.deepcopy(self.andlist[0]),self.s_i,self.s_o)
            # if '?arg_1' in returned_const_declare_in_andlist.keys():
            #     print()
            self.const_declare_in_andlist.update(returned_const_declare_in_andlist)
            # andlist_str = str(self.andlist)
            formula += ''+ andlist_str 
        elif self.type == ':GologSeq': # if ;then
            temp = ''  + 'And(\n    '
            for each in reversed(self.GologSeqNodes):
                temp = temp + each.dump_golog_tree_pre() + ',\n    '
            if temp[-1] == ',':
                temp = temp[:-1]
            formula +=  temp+')' 
        elif self.type == ':GologOr':
            temp = ''  + 'Or(\n    '
            for each in self.GologOrNodes:
                temp = temp + each.dump_golog_tree_pre() + ',\n    '
            if temp[-1] == ',':
                temp = temp[:-1]
            formula +=  temp+')'  
        elif self.type == ':GologPicksExists':
            formula += ''  + 'Exists('+list_args2str(self.PickVars)+'\n    '+ self.ExistsFormula.dump_golog_tree_pre() +')'
        else:
            raise Exception("not such " + self.type)
        return formula

    
    def __str__(self) -> str:
        if self.type ==':GologActTerm':
            return'\n'+ str(self.type) + self.ActionName + '\nAction args is:' + str(self.Actionargs) + '\n'
        elif self.type == 'and':
            return str(self.type) + '\nand:\n'+str(self.andlist)
        elif self.type == ':GologTest':
            return str(self.type) + '\n'+str(self.andlist[0])   
        elif self.type == ':GologIfThen':
            return str(self.type) + '\nIf:\n'+str(self.cond) + '\nThen do:\n'+ str(self.thenlist) 
        elif self.type == ':GologIfElse':
            return str(self.type) + '\nIfElse:\n'+str(self.cond)  + '\nIfTrue:\n'+str(self.ifTrue) +'\nElse false:\n'+str(self.elseFalse) 
        elif self.type == ':GologSeq':
            result = str(self.type) + '\n'
            for each in self.GologSeqNodes:
                result = result + str(each)
            return result
        elif self.type == ':GologOr':
            result = str(self.type) + '\n'
            for each in self.GologOrNodes:
                result = result + str(each)
            return result
        elif self.type == ':GologPicksExists':
            return str(self.type) + '\nvars:'+str(self.PickVars)+'\n'+ str(self.ExistsFormula)
        else:
            raise Exception("not such " + self.type)
            
    def print_pre_eff(self) -> str:
        print(str(self.total_neg_pre) +'\n'+ str(self.total_pos_pre) +'\n'+ str(self.total_neg_eff) +'\n'+ str(self.total_neg_eff))
    
    def set_total_pre_eff(self): # recursive for each situation
        pass      
        

class GologExprTree:
    # @staticmethod
    def recursive_build_golog_tree(self,gologlist):
        """Golog programs contains:
        :GologActTerm
        :GologIfThen
        :GologIfElse
        and
        :GologTest
        :GologSeq
        :GologOr
        :GologPicksExists"""
        temptype = gologlist.pop(0) # :GologActTerm ......
        node = GologNode(temptype,gologlist) # build the Golog Node
        # print(self.total_pos_pre)
        # print(self.total_neg_pre)
        # print(self.total_pos_eff)
        # print(self.total_neg_eff)
        if node.type ==':GologActTerm':
            # print(node.ActionName) 
            # print(node.Actionargs)
            pass
        elif node.type == 'and':
            # print(node.andlist)
            # print(node.neg_andlist)
            # print(node.pos_andlist)
            pass
        elif node.type == ':GologTest':
            # print(node.andlist)
            # print(node.neg_andlist)
            # print(node.pos_andlist)
            pass
        elif node.type == ':GologIfThen':
            # print(node.cond)
            # print(node.thenlist) # list
            node.thenlist = self.recursive_build_golog_tree(node.thenlist) # class <GologNode>
        elif node.type == ':GologIfElse':
            # print(node.cond)
            # print(node.ifTrue)# list-->node
            node.ifTrue = self.recursive_build_golog_tree(node.ifTrue) # class <GologNode>
            # print(node.elseFalse)# list-->node
            node.elseFalse = self.recursive_build_golog_tree(node.elseFalse) # class <GologNode>
        elif node.type == ':GologSeq':
            # print(len(node.GologSeqlist))# list
            for each in node.GologSeqlist:
                node.GologSeqNodes.append(self.recursive_build_golog_tree(each)) # class <GologNode>
            # node.GologSeqNodes_init =  node.GologSeqNodes[:-1] # [delta_1,delta_2,delta_3,...] ==> [':GologSeq', [':GologSeq',delta_1,delta_2,], delta_3]
            # node.GologSeqNodes_tail =  node.GologSeqNodes[-1]  # the last delta_n Golog- Seq[Golog1,Golog2,...]
            if len(node.GologSeqNodes) == 2:
                pass
            elif len(node.GologSeqNodes) > 2:
                pass
            else:
                raise Exception("\'len(node.GologSeqlist) < 0\' is not allow.")
        elif node.type == ':GologOr':
            # print(node.GologOrlist)# list
            for each in node.GologOrlist:
                node.GologOrNodes.append( self.recursive_build_golog_tree(each) )# list of class <GologNode>
        elif node.type == ':GologPicksExists':
            # print(node.PickVars)
            # print(node.ExistsFormula)# list-->node
            node.ExistsFormula = self.recursive_build_golog_tree(node.ExistsFormula) # list of class <GologNode>
        else:
            raise Exception("not such " + node.type)
        return node

    def loop_set_s_i_s_o(self,golog):
        output_split_id = 0# 'Or' node will split s_o into s_o_1,s_o_2,s_o_3,......
        s_id = 0 # numeric identifier for middle situation.we set s'initial situation';s_ 'goal situation'. ther is no 's0' here.initial is 's',goal situation is s_
        set_of_s_io = set() # # set of tuple (s_i,s_o) for every nodes.
        s_act = set() # set of tuple (situation,action) 
        golog.s_i = 's_i'  # s_input  = 's'
        golog.s_o = 's_o' # s_output = 's_'
        golog.const_declare_in_andlist = {} # gologandlitsgolog.const_declare_in_andlist,?arg_6
        from collections import deque
        fathernode = golog
        q = deque([golog])
        # global_situation_tree_mid_act_args_number = 0 #   GologExists GologTestrefinement
        situation_action_args = []# 
        while len(q) > 0:
            curnode = q.pop()
            # print(curnode.type)
            
            if curnode.type ==':GologActTerm':
                # if curnode.ActionName == 'pick':
                #     print()
                if curnode.s_i == '': # had not changed yet
                    curnode.s_i = fathernode.s_i
                if curnode.s_o == '': # had not changed yet
                    curnode.s_o = fathernode.s_o
                set_of_s_io.add((curnode.s_i,curnode.s_o))
                if (curnode.s_i,curnode.ActionName) not in s_act: # the first see this (mid_situation,action)
                    # pddlact_arg-12345... curnode.Actionargs
                    s_act.add((curnode.s_i,curnode.ActionName))#  
                    situation_action_args.append(list((curnode.s_i,curnode.ActionName)) + curnode.Actionargs) # refinementMap
                    # ，‘’， act_arg_123
                # print(curnode.ActionName)
                # print(curnode.Actionargs)
                
            elif curnode.type == 'and': # canceled
                if curnode.s_i == '': # had not changed yet
                    curnode.s_i = fathernode.s_i
                if curnode.s_o == '': # had not changed yet
                    curnode.s_o = fathernode.s_o
                set_of_s_io.add((curnode.s_i,curnode.s_o))
                s_act.add((curnode.s_i,'and')) # test
                situation_action_args.append(list((curnode.s_i,':GologTest')))#！！！！！！！！！！test，“/”
                # print(curnode.andlist)
                # print(curnode.neg_andlist)
                # print(curnode.pos_andlist)
                golog.const_declare_in_andlist.update(curnode.const_declare_in_andlist)# gologandlitsgolog.const_declare_in_andlist,?arg_6
            elif curnode.type == ':GologTest':
                if curnode.s_i == '': # had not changed yet
                    curnode.s_i = fathernode.s_i
                if curnode.s_o == '': # had not changed yet
                    curnode.s_o = fathernode.s_o
                set_of_s_io.add((curnode.s_i,curnode.s_o))
                s_act.add((curnode.s_i,':GologTest'))
                situation_action_args.append(list((curnode.s_i,':GologTest')))
                golog.const_declare_in_andlist.update(curnode.const_declare_in_andlist) # gologandlitsgolog.const_declare_in_andlist,?arg_6
                # print(curnode.andlist)
                # print(curnode.neg_andlist)
                # print(curnode.pos_andlist)

            elif curnode.type == ':GologSeq':
                if curnode.s_i == '': # had not changed yet
                    curnode.s_i = fathernode.s_i
                if curnode.s_o == '': # had not changed yet
                    curnode.s_o = fathernode.s_o
                # set_of_s_io.add((curnode.s_i,curnode.s_o))# Only :Test,:ActionTerm is needed for the Regression,never get this 
                # print(len(curnode.GologSeqNodes))# 
                curnode.GologSeqNodes[0].s_i = curnode.s_i
                curnode.GologSeqNodes[-1].s_o = curnode.s_o
                if len(curnode.GologSeqNodes) <=1:
                    raise Exception('Seq must have elemnts > 1')
                elif len(curnode.GologSeqNodes) == 2:
                        s_id = s_id + 1 #
                        curnode.GologSeqNodes[0].s_o = 's' + str(s_id)
                        curnode.GologSeqNodes[1].s_i = 's' + str(s_id)
                        q.append(curnode.GologSeqNodes[0])
                        q.append(curnode.GologSeqNodes[1])
                        # set_of_s_io.add((curnode.GologSeqNodes[0].s_i,curnode.GologSeqNodes[0].s_o))
                        # set_of_s_io.add((curnode.GologSeqNodes[1].s_i,curnode.GologSeqNodes[1].s_o))
                else:# len(curnode.GologSeqNodes) > 2
                    for index in range(0,len(curnode.GologSeqNodes)):
                        q.append(curnode.GologSeqNodes[index])
                        if index == 0: # the first
                            curnode.GologSeqNodes[index].s_o = 's' + str(s_id)
                        if index == len(curnode.GologSeqNodes)-1: # the last
                            curnode.GologSeqNodes[index].s_i = 's' + str(s_id)
                        # len() > 2
                        if index != 0 and index != len(curnode.GologSeqNodes)-1 : # skip the first s_i/the last s_o  already assigned above
                            s_id = s_id + 1 # s_1，2，3，4，
                            curnode.GologSeqNodes[index].s_i = 's' + str(s_id)
                            curnode.GologSeqNodes[index].s_o = 's' + str(s_id+1) # here had not changed 's_id' yet
                        # set_of_s_io.add((curnode.GologSeqNodes[index].s_i,curnode.GologSeqNodes[index].s_o))# Only :Test,:ActionTerm is needed for the Regression,never get this 
                
            elif curnode.type == ':GologOr':
                if curnode.s_i == '': # had not changed yet
                    curnode.s_i = fathernode.s_i
                if curnode.s_o == '': # had not changed yet
                    curnode.s_o = fathernode.s_o
                # set_of_s_io.add((curnode.s_i,curnode.s_o))# Only :Test,:ActionTerm is needed for the Regression,never get this 
                # print(curnode.GologOrNodes) # 
                for index in range(0,len(curnode.GologOrNodes)):
                    q.append(curnode.GologOrNodes[index])
                    output_split_id = output_split_id + 1
                    curnode.GologOrNodes[index].s_i = curnode.s_i
                    curnode.GologOrNodes[index].s_o = curnode.s_o + '_' + str(output_split_id)
                    # set_of_s_io.add((curnode.s_i,curnode.s_o))# Only :Test,:ActionTerm is needed for the Regression,never get this 
            
            elif curnode.type == ':GologPicksExists':
                if curnode.s_i == '': # had not changed yet
                    curnode.s_i = fathernode.s_i
                if curnode.s_o == '': # had not changed yet
                    curnode.s_o = fathernode.s_o
                # set_of_s_io.add((curnode.s_i,curnode.s_o))# Only :Test,:ActionTerm is needed for the Regression,never get this 
                # print(curnode.PickVars)
                # print(curnode.ExistsFormula)# 
                q.append(curnode.ExistsFormula)
            else:
                raise Exception("not such " + curnode.type)
            fathernode = curnode # update
        golog.set_of_s_io = set_of_s_io# set of tuple (s_i,s_o) for every nodes.
        golog.s_act = s_act # # set of tuple (situation,action) 
        golog.situation_action_args = situation_action_args # [situation action args]


