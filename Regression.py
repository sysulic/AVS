# ==========================================
# Regression
# ==========================================
import copy,json,re

class Regression:
    def __init__(self,domainname,parserinput,qnp_parser,reverse_eachgolog_set_of_s_io_order_list,reverse_situation_tree,eachgolog_set_of_s_act,each_situation_action_args) -> None:
        self.domainname = domainname
        self.each_situation_action_args = each_situation_action_args # [each situation action args]
        def find_golobal_tree_mid_act_args_name2sort():
            golobal_tree_mid_act_args_name2sort  = dict()
            for eachactionmap in parserinput.refinementMap_actionsMap:
                for hig_name,gologtree_for_hig_name in eachactionmap.act_map_golog_dict.items():  # only run one times because"higname --> GologTree with GologNode "
                    # if hig_name == 'put-A-on-B':
                    #     print()
                    tree_mid_act_args_name2sort_for_this_hig_name = dict()
                    for key,val in each_situation_action_args.items():
                        if hig_name == key:
                            for act in parserinput.actions:
                                for s_act_args in val: # nested list
                                    if act.name  == s_act_args[1] :# low action name 
                                        if len(s_act_args[2:]) == 0: # if ':Gologtest' or 'arm-empty' not args predicates
                                            pass
                                        else:
                                            for index in range(2,len(s_act_args)):
                                                tree_mid_act_args_name2sort_for_this_hig_name[s_act_args[index]] = act.parameters[index-2][1]
                    
                    tree_mid_act_args_name2sort_for_this_hig_name.update(gologtree_for_hig_name.const_declare_in_andlist)# gologandlitsgolog.const_declare_in_andlist,?arg_6
                    # GologProgamTreeloop_set_s_iogologgolor_node"and/:GologTest"const_declare_in_andlist，
                    # andlist Nested_list2FOLExp().run_s{}{'?arg_6':'BlockType'}
                    golobal_tree_mid_act_args_name2sort[hig_name] = tree_mid_act_args_name2sort_for_this_hig_name
            return golobal_tree_mid_act_args_name2sort
        self.golobal_tree_mid_act_args_name2sort = find_golobal_tree_mid_act_args_name2sort()# each hig act arrgs name & sort
        self.reverse_eachgolog_set_of_s_io_order_list = reverse_eachgolog_set_of_s_io_order_list
        self.reverse_situation_tree = reverse_situation_tree
        self.eachgolog_set_of_s_act = eachgolog_set_of_s_act # {(situation ,action)}
        self.Dict_Poss_of_acts = [dict(),[]] # [Dict_Poss_of_acts, list of args] # template,not the real one for each action situation tree"json_file_Dict_Poss_of_acts""
        self.Dict_ssa_of_this_act = dict() # [dict(),[]] # [Dict_ssa_of_this_act, dict for each situation action args---specific objects] template,not the real one for each action situation tree"json_file_Dict_ssa_of_this_act""
        self.Dict_situation_tranform_relationship = dict()
        self.parser = parserinput
        self.qnp_parser = qnp_parser
        self.dict_exists = dict()
        self.dict_univer = dict()
        self.generate_poss_file() # generate poss/ssa from pddl parser and write it into json file
        self.generate_ssa_file()


    def get_poss(self,act):
        """poss"""
        temp_args_list = []
        temp_args_list.append(act.name)
        # print(act.positive_preconditions) # [['clear', '?x'], ['on_table', '?x'], ['arm_empty']]
        # print(act.negative_preconditions)
        Poss_of_this_act_left = "Poss("
        Poss_of_this_act_left += (act.name + '(')
        # print(act.parameters) #[['?x', 'BlockType']]
        for each in act.parameters:
            for member in each:
                if member[0] == '?':
                    Poss_of_this_act_left += member[1:]
                    Poss_of_this_act_left +=','
                    if member[1:] not in temp_args_list:
                        temp_args_list.append(member[1:])
        Poss_of_this_act_left = Poss_of_this_act_left[:-1]
        Poss_of_this_act_left += ')'
        Poss_of_this_act_left += ",s)" 
        # if "one step" regression,need not this,just generate 'arm_empty()' means 'arm_empty()[s]' ,as well as 'arm_empty(s)'
        Poss_of_this_act_right = "And("
        for each in act.positive_preconditions:
            Poss_of_this_act_right += each[0]
            Poss_of_this_act_right += '('
            for member in each[1:]:# domain.pddl will never apear 'A/B/LEFT/RGIHT',but always '?x/?y'
                if member[0] == '?':
                    Poss_of_this_act_right += (member[1:] + ',')
                    if member[1:] not in temp_args_list:
                        temp_args_list.append(member[1:])
            # Poss_of_this_act_right = Poss_of_this_act_right[:-1]
            Poss_of_this_act_right += 's),'
        for each in act.negative_preconditions:
            Poss_of_this_act_right += 'Not('+each[0]
            Poss_of_this_act_right += '('
            for member in each[1:]:
                if member[0] == '?': # domain.pddl will never apear 'A/B/LEFT/RGIHT',but always '?x/?y'
                    Poss_of_this_act_right += (member[1:] + ',')
                    if member[1:] not in temp_args_list:
                        temp_args_list.append(member[1:])
            Poss_of_this_act_right += 's)),'
        Poss_of_this_act_right = Poss_of_this_act_right[:-1]
        Poss_of_this_act_right += ')'
        self.Dict_Poss_of_acts[0][Poss_of_this_act_left] = Poss_of_this_act_right
        self.Dict_Poss_of_acts[1].append(temp_args_list)
    
    def show_get_poss(self):
        print("Dict_Poss_of_acts is:\n")
        print(self.Dict_Poss_of_acts[0])


    def generate_poss_file(self):
        """，Poss"""
        for act in self.parser.actions:# low level action
            self.get_poss(act) # generate poss/ssa from pddl parser
        for act in self.qnp_parser.actionlist: # hig
            for key,situation_list in self.reverse_eachgolog_set_of_s_io_order_list.items():
                if act.name == key:
                    tempdict = dict()
                    cp_Dict_Poss_of_acts = copy.deepcopy(self.Dict_Poss_of_acts)
                    for each in situation_list:
                        tempPossMap = copy.deepcopy(self.Dict_Poss_of_acts[0])
                        for key,val in tempPossMap.items():
                            key = key.replace(',s)',','+each+')')
                            val = val.replace(',s)',','+each+')')
                            key = key.replace('(s)','('+each+')')
                            val = val.replace('(s)','('+each+')')
                            tempdict[key] = val
                    cp_Dict_Poss_of_acts[0] = tempdict
                    # self.show_get_poss() # show_get_poss here
                    json_file_Dict_Poss_of_acts = "./autogenerated/{0}_Dict_Poss_of_act_{1}.json".format(self.domainname,act.name)
                    with open(json_file_Dict_Poss_of_acts, mode='w',encoding='utf-8') as fs:
                            fs.write(json.dumps(cp_Dict_Poss_of_acts,ensure_ascii=False,indent=1))
            

    # test regerssion
    def one_step_poss_regression(self,test_phi_formula,lowaction,domainname,hig_action_name,s_i):# action is 'low level action name'
        """one_step_poss_regression"""
        
        tempobj = {}
        json_file_Dict_Poss_of_acts = "./autogenerated/{0}_Dict_Poss_of_act_{1}.json".format(domainname,hig_action_name)
        with open(json_file_Dict_Poss_of_acts, mode='r',encoding='utf-8') as fs:
            tempobj = json.load(fs)
        # print(f'contents readed from {json_file_Dict_Poss_of_acts}is :\n')
        Dict_Poss_of_acts = tempobj # temp for read to test many function

        test_phi_formula_actions_match_Obj = re.findall( r'Poss\('+lowaction+'\(([^()]*?)\),'+s_i+'\)', test_phi_formula, re.M)
        if len(test_phi_formula_actions_match_Obj) == 0:# ，[] arm_empty()，，：，golog，
            return test_phi_formula # can not find this action and need not to replace "POSS"
        for everyMatchOne in test_phi_formula_actions_match_Obj:
            args = everyMatchOne # 'x,y' 
            # test_phi_formula_actions_match_Obj.group(1) # args string in the input formula we want # not only once 
            for key ,value in Dict_Poss_of_acts[0].items():
                matchObj = re.match( r'Poss\((.*)\(.*\),(s.*)\)', key, re.M|re.I)
                if matchObj.group(1) == lowaction and matchObj.group(2) == s_i:
                    for each in Dict_Poss_of_acts[1]:
                        if each[0] == lowaction:
                            args_in_dict = ''# string 'ob,underob,'
                            for eachone in each[1:]:# each[0] == actionName + ['x', 'y']
                                args_in_dict += (eachone+',')
                            args_in_dict = args_in_dict[:-1]# string 'ob,underob'
                            args_list = args.split(",")# 
                            if len(args_list) != len(args_in_dict.split(",")):
                                raise Exception('length of args is not align.')
                            key_replace = key.replace(args_in_dict,args)
                            for index in range(0,len(args_list)):#['a', 'b'] /['A', 'B']
                                arg_old = each[index+1]+','# each: ['stack', 'ob', 'underob']
                                arg_new = args_list[index]+','# args_list ['A', 'B']

                                value = value.replace('('+arg_old,'('+arg_new)#
                                value = value.replace(','+arg_old,','+arg_new)#
                            test_phi_formula = test_phi_formula.replace(key_replace,value)
                            return test_phi_formula

    def get_ssa(self):
        """ssa"""
        for eachactionmap in self.parser.refinementMap_actionsMap:
            for hig_name,_ in eachactionmap.act_map_golog_dict.items():  # only run one times because"higname --> GologTree with GologNode "
                temp_dict = dict()
                for s_o,s_input in self.reverse_situation_tree[hig_name].items():
                    if len(s_input) == 0: # 's_i' --> []
                        continue # skip
                    for situation_action_args in self.each_situation_action_args[hig_name]:
                        if s_input[0] == situation_action_args[0]:
                            correct_list =  [situation_action_args[1]]
                            if situation_action_args[1] == ':Gologtest' and len(situation_action_args[2:]) == 0:
                                # ':GologTest'.low action always args:
                                correct_list.append(s_input[0])
                            else:
                                temp_action_list = []
                                for args in situation_action_args[2:]:
                                    temp_action_list.append(args)
                                correct_list.append(s_input[0]) 
                                correct_list.append(temp_action_list) # args 
                    temp_dict[s_o] = correct_list
                self.Dict_situation_tranform_relationship[hig_name] = temp_dict
        import networkx as nx
        import matplotlib.pyplot as plt
        def draw_situation_translate(each_hig_name,picture_dict):
            # G = nx.Graph()
            G = nx.DiGraph()
            G.clear()
            s_set = set()
            s_set.clear()
            for s_output,act_s_input_args_list in picture_dict.items():
                s_set.add(s_output)
                s_set.add(act_s_input_args_list[1])
            for each in s_set:
                G.add_node('{0}'.format(each),desc = '{0}'.format(each))
            for s_output,act_s_input_args_list in picture_dict.items():
                G.add_edge(s_output,act_s_input_args_list[1],name='{0}{1}'.format(act_s_input_args_list[0],str(act_s_input_args_list[2:][0])))

            #draw graph with labels
            # pos = nx.spring_layout(G)# ，
            random_pos = nx.random_layout(G, seed=42)
            pos = nx.spring_layout(G, pos=random_pos)
            nx.draw(G, pos)
            node_labels = nx.get_node_attributes(G, 'desc')
            nx.draw_networkx_labels(G, pos, labels=node_labels)
            edge_labels = nx.get_edge_attributes(G, 'name')
            nx.draw_networkx_edge_labels(G, pos, edge_labels=edge_labels)
            plt.savefig("./autogenerated/{0}_order_of_regression.png".format(each_hig_name))
            # plt.show()
            plt.clf()   # Clear figure
        for each_hig_name ,picture_dict in self.Dict_situation_tranform_relationship.items():
            draw_situation_translate(each_hig_name,picture_dict)

        # ssa
        for eachactionmap in self.parser.refinementMap_actionsMap:# 
            for hig_name,_ in eachactionmap.act_map_golog_dict.items(): # only once because [hig_name-->golog]# reverse hig_action_name ==> Dictssa_
                for hig_name_s,act_s_args_list in self.Dict_situation_tranform_relationship.items():#golog 
                    if hig_name == hig_name_s:
                        ssa_for_this_hig_name_act = dict() 
                        for situation_after_act,act_s_args in act_s_args_list.items():
                            # --‘act_s_args’，，，
                            act_name = act_s_args[0] # act_name:'unstack'
                            # act_name ：Gologtest，，
                            situation_before_act = act_s_args[1]#s1
                            act_args_under_situation = act_s_args[2] # args_*if ':gologTest'-->[] 
                                                        
                            # act_args in specific situation act_args_under_situationstack(act_args_2,act_arg_3)
                            for predicate,args_and_sort in self.parser.predicates.items():
                                # predicate   ssa
                                                                                        
                                # left
                                cur_ssa_left = predicate + '('
                                pddl_predicate_args = '' # pddl domain ?x-Blocktype,?y-BlockType.
                                if len(args_and_sort) == 0:
                                    cur_ssa_left = cur_ssa_left  + situation_after_act +')'
                                else:
                                    for each in args_and_sort: # arm-empty()==0,domain?
                                        if each[0] == '?':
                                            pddl_predicate_args = pddl_predicate_args + each[1:] + ','# ，，
                                    if pddl_predicate_args[-1] == ',':
                                        pddl_predicate_args = pddl_predicate_args[:-1]
                                    cur_ssa_left = cur_ssa_left + pddl_predicate_args + ',' + situation_after_act +')'
         
                                # right
                                pddl_predicate_args_list = pddl_predicate_args.split(',') # ?x,?y
                                if pddl_predicate_args_list == ['']:
                                    pddl_predicate_args_list = []
                                
                                # for transitive_closure_fml, for specific 'tcfml'
                                # 'before' will never change for const case like Findnext and so on.
                                if(self.parser.predicates_transitive_closure_fml != {}):
                                    # tcfml --> tc_predicate --> prototype_predictae
                                    tc_ssa_left = ""
                                    tc_ssa_right = ""
                                    for tc_predicate,prototype_predicate in self.parser.predicates_transitive_closure.items():
                                        if(prototype_predicate == predicate):
                                            tc_ssa_left = cur_ssa_left.replace(prototype_predicate,tc_predicate)
                                            tc_ssa_right = tc_ssa_left.replace(situation_after_act,situation_before_act)
                                            ssa_for_this_hig_name_act[tc_ssa_left] = tc_ssa_right

                                # 1
                                cur_ssa_right = ''# ssa
                                if act_name == ':GologTest':
                                    cur_ssa_right = cur_ssa_left.replace(situation_after_act,situation_before_act)# 
                                    ssa_for_this_hig_name_act[cur_ssa_left] = cur_ssa_right
                                    continue 
                                    # ':Gologtest'
                                # 2 GologTest
                                
                                for act in self.parser.actions:
                                    region_predicate_args_pddl = '' 
                                    def whether_predicate_in_effect_list(predicate,eff_list):#'region_predicate_args_pddl'return
                                        nonlocal region_predicate_args_pddl# region_predicate_args_pddl 
                                        for each in eff_list:
                                            if predicate == each[0]:# DEL/ADD effect list
                                                for args in each[1:]:
                                                    region_predicate_args_pddl = region_predicate_args_pddl + args[1:] + ','# 
                                                if len(region_predicate_args_pddl) != 0 and region_predicate_args_pddl[-1] == ',':
                                                    region_predicate_args_pddl = region_predicate_args_pddl[:-1]
                                                return True
                                        return False # prediacte "not in" eff_list means: this line will be exec
                                    if act.name == act_name :                                   
                                        region_predicate_args_pddl = '' # 
                                        Flag_del = whether_predicate_in_effect_list(predicate,act.del_effects)
                                        region_predicate_args_pddl = '' # 
                                        Flag_add = whether_predicate_in_effect_list(predicate,act.add_effects)
                                        # 1 add,del
                                        if Flag_add == True and Flag_del == False:
                                            region_predicate_args_pddl = '' # 
                                            whether_predicate_in_effect_list(predicate,act.add_effects)
                                            #  region_predicate_args_pddl 
                                            region_predicate_args_pddl_list = region_predicate_args_pddl.split(',') # 
                                            region_act_args_pddl = ''
                                            for actArgs_sort_list in act.parameters:# stack(obj,underobj)
                                                for actArgs_or_sort in actArgs_sort_list:
                                                    if actArgs_or_sort[0] == '?':
                                                        region_act_args_pddl = region_act_args_pddl + actArgs_or_sort[1:]+','
                                            if region_act_args_pddl[-1] == ',':
                                                region_act_args_pddl = region_act_args_pddl[:-1]
                                            region_act_args_pddl_list = region_act_args_pddl.split(',')
                                            Out_of_Order_array = []
                                            for each in region_predicate_args_pddl_list:
                                                if each in region_act_args_pddl_list:
                                                    index_in_region_act_args_pddl_list = region_act_args_pddl_list.index(each)# '' is not list
                                                    Out_of_Order_array.append(index_in_region_act_args_pddl_list)
                                            rearrange_act_args_under_situation_2_predicateorder = [] 
                                            for mixed_index_value in Out_of_Order_array:
                                                rearrange_act_args_under_situation_2_predicateorder.append(act_args_under_situation[mixed_index_value])
                                            
                                            # ==============================================
                                            predicate_args_eq_respectively = '' #  ,，，，
                                            for index in range(0,len(rearrange_act_args_under_situation_2_predicateorder)):#  ，.len(pddl_predicate_args_list)
                                                predicate_args_eq_respectively = predicate_args_eq_respectively + pddl_predicate_args_list[index] + '==' + rearrange_act_args_under_situation_2_predicateorder[index] +','
                                            if len(rearrange_act_args_under_situation_2_predicateorder) == 0:# arm_empty
                                                # $s_i$，
                                                cur_ssa_right = cur_ssa_right + 'Not(' + predicate +'(' + pddl_predicate_args + situation_before_act + '))'
                                            else:
                                                predicate_args_eq_respectively = predicate_args_eq_respectively[:-1]# del the last ','
                                                if len(predicate_args_eq_respectively.split(','))>1 :
                                                    cur_ssa_right = cur_ssa_right + 'Or(' \
                                                    + 'And('+'Not('+predicate + '('+pddl_predicate_args+ ','+situation_before_act +')),And('+ predicate_args_eq_respectively +')),' + \
                                                    'And(' + predicate + '(' + pddl_predicate_args + ','+situation_before_act + '),Not(And(' + predicate_args_eq_respectively +')))' + \
                                                    ')'
                                                elif len(predicate_args_eq_respectively.split(','))==1:
                                                    cur_ssa_right = cur_ssa_right + 'Or(' \
                                                    + 'And('+'Not('+predicate + '('+pddl_predicate_args+ ','+situation_before_act +')),'+ predicate_args_eq_respectively +'),' + \
                                                    'And(' + predicate + '(' + pddl_predicate_args + ','+situation_before_act + '),Not(' + predicate_args_eq_respectively +'))' + \
                                                    ')'
                                                else: 
                                                    raise Exception('impossible')

                                        # 2 del,add
                                        elif Flag_del == True and Flag_add == False:
                                            region_predicate_args_pddl = '' # 
                                            whether_predicate_in_effect_list(predicate,act.del_effects)
                                    
                                            #  region_predicate_args_pddl 
                                            region_predicate_args_pddl_list = region_predicate_args_pddl.split(',') # 
                                            region_act_args_pddl = ''
                                            for actArgs_sort_list in act.parameters:# stack(obj,underobj)
                                                for actArgs_or_sort in actArgs_sort_list:
                                                    if actArgs_or_sort[0] == '?':
                                                        region_act_args_pddl = region_act_args_pddl + actArgs_or_sort[1:]+','# 
                                            if region_act_args_pddl[-1] == ',':
                                                region_act_args_pddl = region_act_args_pddl[:-1]
                                            region_act_args_pddl_list = region_act_args_pddl.split(',')# 'x,y'
                                            Out_of_Order_array = []
                                            for each in region_predicate_args_pddl_list:
                                                if each in region_act_args_pddl_list:
                                                    index_in_region_act_args_pddl_list = region_act_args_pddl_list.index(each)# '' is not list
                                                    Out_of_Order_array.append(index_in_region_act_args_pddl_list)
                                            # ！
                                            rearrange_act_args_under_situation_2_predicateorder = [] 
                                            # arg123() 
                                            #  “?x,?ySSA pddl_predicate_args_list ” 
                                            for mixed_index_value in Out_of_Order_array:
                                                rearrange_act_args_under_situation_2_predicateorder.append(act_args_under_situation[mixed_index_value])
                                            
                                            # ==============================================
                                            predicate_args_eq_respectively = '' #  
                                            for index in range(0,len(rearrange_act_args_under_situation_2_predicateorder)):
                                                #  ，.len(pddl_predicate_args_list)
                                                predicate_args_eq_respectively = predicate_args_eq_respectively + pddl_predicate_args_list[index] + '==' + rearrange_act_args_under_situation_2_predicateorder[index] +','
                                            if len(rearrange_act_args_under_situation_2_predicateorder) == 0:# arm_empty
                                                cur_ssa_right = cur_ssa_left.replace(situation_after_act,situation_before_act)
                                                cur_ssa_left = 'Not('+cur_ssa_left+')'# negative 
                                            else:
                                                predicate_args_eq_respectively = predicate_args_eq_respectively[:-1]# del the last ','
                                                if len(predicate_args_eq_respectively.split(',')) > 1:
                                                    cur_ssa_right = cur_ssa_right +'And(' + predicate + '(' + pddl_predicate_args + ','+situation_before_act + '),Not(And(' + predicate_args_eq_respectively +')))' 
                                                else:# len(predicate_args_eq_respectively.split(',')) == 1 
                                                    cur_ssa_right = cur_ssa_right +'And(' + predicate + '(' + pddl_predicate_args + ','+situation_before_act + '),Not(' + predicate_args_eq_respectively +'))' 

                                        # 3 ，
                                        elif Flag_add == True and Flag_del == True:
                                            region_predicate_args_pddl = '' # 
                                            whether_predicate_in_effect_list(predicate,act.del_effects)

                                            region_predicate_args_pddl_del = region_predicate_args_pddl # delNot(at-robby('fromroom')'fromroom'
                                            region_predicate_args_pddl_del_list = region_predicate_args_pddl_del.split(',') # 
                                            region_act_args_pddl = ''
                                            for actArgs_sort_list in act.parameters:# stack(obj,underobj)
                                                for actArgs_or_sort in actArgs_sort_list:
                                                    if actArgs_or_sort[0] == '?':
                                                        region_act_args_pddl = region_act_args_pddl + actArgs_or_sort[1:]+','# 
                                            if region_act_args_pddl[-1] == ',':
                                                region_act_args_pddl = region_act_args_pddl[:-1]
                                            region_act_args_pddl_list = region_act_args_pddl.split(',')# pddl action "move"'fromroom,toroom'【0，1】

                                            Out_of_Order_array_del = []
                                            for each in region_predicate_args_pddl_del_list:
                                                if each in region_act_args_pddl_list:
                                                    index_in_region_act_args_pddl_list = region_act_args_pddl_list.index(each)# '' is not list
                                                    Out_of_Order_array_del.append(index_in_region_act_args_pddl_list)
                                            # ！
                                            rearrange_act_args_under_situation_2_predicateorder_del = [] 
                                            for mixed_index_value in Out_of_Order_array_del:
                                                rearrange_act_args_under_situation_2_predicateorder_del.append(act_args_under_situation[mixed_index_value])

                                            
                                            region_predicate_args_pddl = '' # 
                                            whether_predicate_in_effect_list(predicate,act.add_effects)
                                            #  region_predicate_args_pddl_del add
                                            region_predicate_args_pddl_add = region_predicate_args_pddl # del
                                            region_predicate_args_pddl_add_list = region_predicate_args_pddl_add.split(',') # 
                                            region_act_args_pddl = ''
                                            for actArgs_sort_list in act.parameters:# stack(obj,underobj)
                                                for actArgs_or_sort in actArgs_sort_list:
                                                    if actArgs_or_sort[0] == '?':
                                                        region_act_args_pddl = region_act_args_pddl + actArgs_or_sort[1:]+','# 
                                            if region_act_args_pddl[-1] == ',':
                                                region_act_args_pddl = region_act_args_pddl[:-1]
                                            region_act_args_pddl_list = region_act_args_pddl.split(',')# 'x,y'
                                            Out_of_Order_array_add = []
                                            for each in region_predicate_args_pddl_add_list:
                                                if each in region_act_args_pddl_list:# ['v', 'l1', 'l2'] --> 0，2
                                                    index_in_region_act_args_pddl_list = region_act_args_pddl_list.index(each)# '' is not list
                                                    Out_of_Order_array_add.append(index_in_region_act_args_pddl_list)
                                            # ！
                                            rearrange_act_args_under_situation_2_predicateorder_add = [] 
                                            for mixed_index_value in Out_of_Order_array_add:
                                                rearrange_act_args_under_situation_2_predicateorder_add.append(act_args_under_situation[mixed_index_value])
                                            #  act_args_under_situation ，
                                            #   add  rearrange_act_args_under_situation_2_predicateorder_add ['A']

                                            # ==============================================
                                            # DelAdd：
                                            predicate_args_eq_respectively_del = '' # del
                                            for index in range(0,len(rearrange_act_args_under_situation_2_predicateorder_del)):#  rearrange_act_args_under_situation_2_predicateorder_del
                                                predicate_args_eq_respectively_del += pddl_predicate_args_list[index] + '==' + rearrange_act_args_under_situation_2_predicateorder_del[index] +','
                                            predicate_args_eq_respectively_add = '' # add
                                            for index in range(0,len(rearrange_act_args_under_situation_2_predicateorder_add)):#  rearrange_act_args_under_situation_2_predicateorder_add
                                                predicate_args_eq_respectively_add += pddl_predicate_args_list[index] + '==' + rearrange_act_args_under_situation_2_predicateorder_add[index] +','
                                            
                                            if len(rearrange_act_args_under_situation_2_predicateorder_add) == 0:# arm_empty # 
                                                cur_ssa_right = cur_ssa_left.replace(situation_after_act,situation_before_act)
                                                cur_ssa_left = 'Not('+cur_ssa_left+')'# negative 
                                            else:# ，pddl_predicate_args ‘?x,?y’
                                                predicate_args_eq_respectively_del = predicate_args_eq_respectively_del[:-1]# delete the last ','
                                                predicate_args_eq_respectively_add = predicate_args_eq_respectively_add[:-1]# delete the last ','
                                                if len(predicate_args_eq_respectively_del.split(','))>1 and len(predicate_args_eq_respectively_add.split(',')) > 1:
                                                    cur_ssa_right += 'Or(' + \
                                                    'And('+'Not('+predicate + '('+pddl_predicate_args+ ','+situation_before_act +')),And('+ predicate_args_eq_respectively_add +')),' + \
                                                    'And(' + predicate + '(' + pddl_predicate_args + ','+situation_before_act + '),Not(And(' + predicate_args_eq_respectively_del +')))' + \
                                                    ')'
                                                elif len(predicate_args_eq_respectively_del.split(','))==1 and len(predicate_args_eq_respectively_add.split(',')) == 1: # == 1 mean need not 'And()'
                                                    cur_ssa_right += 'Or(' + \
                                                    'And('+'Not('+predicate + '('+pddl_predicate_args+ ','+situation_before_act +')),'+ predicate_args_eq_respectively_add +'),' + \
                                                    'And(' + predicate + '(' + pddl_predicate_args + ','+situation_before_act + '),Not(' + predicate_args_eq_respectively_del +'))' + \
                                                    ')'
                                                elif len(predicate_args_eq_respectively_del.split(','))>1 and len(predicate_args_eq_respectively_add.split(',')) == 1: # == 1 mean need not 'And()'
                                                    cur_ssa_right += 'Or(' + \
                                                    'And('+'Not('+predicate + '('+pddl_predicate_args+ ','+situation_before_act +')),'+ predicate_args_eq_respectively_add +'),' + \
                                                    'And(' + predicate + '(' + pddl_predicate_args + ','+situation_before_act + '),Not(And(' + predicate_args_eq_respectively_del +')))' + \
                                                    ')'
                                                elif len(predicate_args_eq_respectively_del.split(','))==1 and len(predicate_args_eq_respectively_add.split(',')) == 1: # == 1 mean need not 'And()'
                                                    cur_ssa_right += 'Or(' + \
                                                    'And('+'Not('+predicate + '('+pddl_predicate_args+ ','+situation_before_act +')),And('+ predicate_args_eq_respectively_add +')),' + \
                                                    'And(' + predicate + '(' + pddl_predicate_args + ','+situation_before_act + '),Not(' + predicate_args_eq_respectively_del +'))' + \
                                                    ')'
                                                else :
                                                    raise Exception('impossible')

                                        # 4 
                                        else:
                                            cur_ssa_right = cur_ssa_left.replace(situation_after_act,situation_before_act)# ，":GologTest"
                                        ssa_for_this_hig_name_act[cur_ssa_left] = cur_ssa_right
                        self.Dict_ssa_of_this_act[hig_name] = ssa_for_this_hig_name_act
        json_file_Dict_ssa_of_this_act = "./autogenerated/{0}_Dict_ssa_template_for_variables_args.json".format(self.domainname)
        with open(json_file_Dict_ssa_of_this_act, mode='w',encoding='utf-8') as fs:
                fs.write(json.dumps(self.Dict_ssa_of_this_act,ensure_ascii=False,indent=1))    
   
    def generate_ssa_file(self):
        """ssa"""
        self.get_ssa()
 
    def one_step_ssa_regression(self,test_psi_formula,predicate,domainname,hig_action_name,s_i):
        """one_step_ssa_regression given 'predicate' and 'formula'"""
        # get Dict_ssa_of_this_act
        tempobj = {}
        json_file_Dict_ssa_of_this_act = "./autogenerated/{0}_Dict_ssa_template_for_variables_args.json".format(self.domainname)
        with open(json_file_Dict_ssa_of_this_act, mode='r') as fs:
            tempobj = json.load(fs)
        # print(f'contents readed from {json_file_Dict_ssa_of_this_act}is :\n')
        Dict_ssa_of_this_act_readed = tempobj # temp for read to test many function
        Dict_ssa_of_this_act = Dict_ssa_of_this_act_readed # 'impossible'
 
        self.Dict_ssa_of_this_act = Dict_ssa_of_this_act
        psi_formula_match_Obj_predicate = re.findall( r''+predicate +'\(([^()]*?),?(s[^,()]*)'+'\)', test_psi_formula, re.M)
        
        for hig_name,ssa in Dict_ssa_of_this_act.items():
            if hig_action_name == hig_name:#ssa
                for eachtuple in psi_formula_match_Obj_predicate:
                    predicate_args = eachtuple[0]
                    situation_after_action = eachtuple[1]
                    if predicate_args == '':# zero args
                        # dict_left :"arm_empty(s1)"           # variables_in_dict_left_list,ssa
                        # left_to_find :"arm_empty(s1)"        # predicate_args_list 
                        left_to_find = predicate + '(' + "" + situation_after_action + ')'
                        for dict_left,dict_right in Dict_ssa_of_this_act[hig_name].items():
                            if left_to_find == dict_left:
                                test_psi_formula = test_psi_formula.replace(left_to_find,dict_right)
                        left_to_find = 'Not('+predicate + '(' + "" + situation_after_action + ')' +')'
                        for dict_left,dict_right in Dict_ssa_of_this_act[hig_name].items():
                            if left_to_find == dict_left:
                                test_psi_formula = test_psi_formula.replace(left_to_find,dict_right)

                    else: # predicate has args > 0
                        # dict_left    :"on(x,y,s1)"                        # variables_in_dict_left_list,ssa
                        # left_to_find :"on(act_arg_1,act_arg_2,s1)"        # predicate_args_list 
                        left_to_find = predicate + '(' + predicate_args + ',' + situation_after_action + ')'
                        for dict_left,dict_right in Dict_ssa_of_this_act[hig_name].items():
                            predicate_args_list = predicate_args.split(',')
                            variables_in_dict_left_list = re.findall( r''+predicate +'\(([^()]*?),'+situation_after_action+'\)', dict_left, re.M)
                            if variables_in_dict_left_list == []:# ，
                                continue
                            else: # 
                                variables_in_dict_left_list = variables_in_dict_left_list[0].split(',')# '?x'
                                # dict_left :"clear(x,s1)"           
                                # # variables_in_dict_left_list,ssa x,y

                                # left_to_find :"clear(act_arg_1,s1)" 
                                # # predicate_args_list  act_arg_1,act_arg_2
                                dict_left_replace = dict_left
                                dict_right_replace = dict_right
                                for index in range(0,len(predicate_args_list)):
                                    dict_left_replace  = dict_left_replace.replace('(' + variables_in_dict_left_list[index] + ',','(' + predicate_args_list[index]+',')
                                    dict_right_replace = dict_right_replace.replace('(' + variables_in_dict_left_list[index]+ ',','(' + predicate_args_list[index]+',')
                                    dict_left_replace  = dict_left_replace.replace(',' + variables_in_dict_left_list[index] + ',',',' + predicate_args_list[index]+',')
                                    dict_right_replace = dict_right_replace.replace(',' + variables_in_dict_left_list[index]+ ',',',' + predicate_args_list[index]+',')

                                    dict_left_replace  = dict_left_replace.replace(','+variables_in_dict_left_list[index]  + '==',','+predicate_args_list[index]+'==')
                                    dict_right_replace = dict_right_replace.replace(','+variables_in_dict_left_list[index] + '==',','+predicate_args_list[index]+'==')
                                    dict_left_replace  = dict_left_replace.replace('('+variables_in_dict_left_list[index]  + '==','('+predicate_args_list[index]+'==')
                                    dict_right_replace = dict_right_replace.replace('('+variables_in_dict_left_list[index] + '==','('+predicate_args_list[index]+'==')
                                    # '==' + room + ')'
                                    dict_left_replace  = dict_left_replace.replace( '=='+variables_in_dict_left_list[index]+')','=='+predicate_args_list[index]+')')
                                    dict_right_replace = dict_right_replace.replace('=='+variables_in_dict_left_list[index]+')','=='+predicate_args_list[index]+')')
                                    # !=
                                    dict_left_replace  = dict_left_replace.replace(','+variables_in_dict_left_list[index]  + '!=',','+predicate_args_list[index]+'!=')
                                    dict_right_replace = dict_right_replace.replace(','+variables_in_dict_left_list[index] + '!=',','+predicate_args_list[index]+'!=')
                                    dict_left_replace  = dict_left_replace.replace('('+variables_in_dict_left_list[index]  + '1=','('+predicate_args_list[index]+'!=')
                                    dict_right_replace = dict_right_replace.replace('('+variables_in_dict_left_list[index] + '!=','('+predicate_args_list[index]+'!=')
                                    # '!=' + room + ')'
                                    dict_left_replace  = dict_left_replace.replace( '!='+variables_in_dict_left_list[index]+')','!='+predicate_args_list[index]+')')
                                    dict_right_replace = dict_right_replace.replace('!='+variables_in_dict_left_list[index]+')','!='+predicate_args_list[index]+')')
                                    #  dict_left_replace  = dict_left_replace.replace(','+variables_in_dict_left_list[index]  + ')',','+predicate_args_list[index]+')')
                    
                                if left_to_find == dict_left_replace:
                                    test_psi_formula = test_psi_formula.replace(left_to_find,dict_right_replace)# 
        return test_psi_formula

    import re
    # the main Regression function entrance:
    def one_step_regression_with_all_poss_ssa(self,test_formula,hig_action_name,s_i):
        """Input a formula,return the formula after one_step_regression_with_all_poss_ssa"""
        # 1. \mathcal{D}_{poss}:for all action one_step_poss_regression
        for act in self.parser.actions:
            test_formula = self.one_step_poss_regression(test_formula,act.name,self.parser.domain_name,hig_action_name,s_i) # action --> poss
        # 2. \mathcal{D}_{ssa}:for all predicates one_step_ssa_regression
        for predicate,_ in self.parser.predicates.items():
            test_formula = self.one_step_ssa_regression(test_formula,predicate       ,self.parser.domain_name,hig_action_name,s_i)
            
            #! for transitive_closure_fml, for specific 'tcfml'
            # 'before' will never change for const case like Findnext and so on.
            if(self.parser.predicates_transitive_closure_fml != {}):
                # tcfml --> tc_predicate --> prototype_predictae
                for tc_predicate,prototype_predicate in self.parser.predicates_transitive_closure.items():
                    if re.findall(tc_predicate,test_formula):
                        if(prototype_predicate == predicate):
                            test_formula = self.one_step_ssa_regression(test_formula,tc_predicate,self.parser.domain_name,hig_action_name,s_i)
        
        # 3. \mathcal{D}_{una}:do not simplify here but wait for output get it simplied by z3-solver to cancel the nested duplicated terms.
        return test_formula
    
    def loop_regression_with_all_poss_ssa(self,test_formula,hig_action_name):
        """Input a formula,return the formula after loop multiple_steps_regression_with_all_poss_ssa"""
        for hig_name_in_dict,each_s_output_list in self.reverse_eachgolog_set_of_s_io_order_list.items():
            if hig_name_in_dict == hig_action_name:
                for each_s_output in each_s_output_list:
                    for hig_name,s_o2s_i in self.reverse_situation_tree.items():
                        if hig_name == hig_action_name:
                            for s_o,s_i_list in s_o2s_i.items():
                                if s_o == each_s_output and s_i_list != []:# s_i_list ==[] means s_input == 's_i' ,the end.
                                    s_input = s_i_list[0]
                                    test_formula = self.one_step_regression_with_all_poss_ssa(test_formula,hig_name,s_input)
        return test_formula# maybe "Impossible"

    def dump_regression_exists(self,predicate_args_str_or_formula_returned,golog_node,hig_name) -> str:
        """"""
        from GologProgramTree import Nested_list2FOLExp
        formula = ""
        predicate_args_str_or_formula_returned = predicate_args_str_or_formula_returned.replace(',s_o)',','+golog_node.s_o+')')
        predicate_args_str_or_formula_returned = predicate_args_str_or_formula_returned.replace('(s_o)','('+golog_node.s_o+')') # arm_empty(s_o)
        #'s_o'()gologself.s_o，Ors_o_1/s_o_2
        def list_args2str(argslist):# Picks
            args2str = '['
            for each in argslist:
                args2str+=each+','
            if args2str[-1] == ',':
                args2str = args2str[:-1]
            args2str+='],'
            return args2str
        def actionlist2str(ActionName,actiontermlist,s_i): # ActionTerm
            actiontermlist_str = 'Poss('+ActionName + '('
            if len(actiontermlist) >= 1:# ，
                for each in actiontermlist:
                    if each[0] == '?':
                        actiontermlist_str += each[1:] + ',' # ?x ?y
                    else:
                        actiontermlist_str += each + ',' # A,B,LEFT,RIGHT
                if actiontermlist_str[-1] == ',':# 
                    actiontermlist_str = actiontermlist_str[:-1]
            actiontermlist_str += ')'+','+ s_i +')'# 
            return actiontermlist_str
        if golog_node.type ==':GologActTerm':
            formula ='And(\n    '+ actionlist2str(golog_node.ActionName,golog_node.Actionargs,golog_node.s_i) +\
                ',\n    ' + predicate_args_str_or_formula_returned+')'
            formula = self.one_step_regression_with_all_poss_ssa(formula,hig_name,golog_node.s_i)
            #  hig_name 
        elif golog_node.type == ':GologTest':
            andlist_str,_ = Nested_list2FOLExp().run_s(copy.deepcopy(golog_node.andlist[0]),golog_node.s_i,golog_node.s_o)# 's_o'，'s_i'
            formula = 'And(\n    '+ andlist_str +',\n    '+ predicate_args_str_or_formula_returned  +')' 
        elif golog_node.type == ':GologSeq': # if ;then
            nested_return_formula = predicate_args_str_or_formula_returned #  on(x,y,s_o)/'Not(at_robby(B,s_o))'...
            for each in reversed(golog_node.GologSeqNodes):
                nested_return_formula = self.dump_regression_exists(nested_return_formula,each,hig_name)
            formula = nested_return_formula
        elif golog_node.type == ':GologOr':
            temp = 'Or(\n    '# difference!
            for each in golog_node.GologOrNodes:
                temp += self.dump_regression_exists(predicate_args_str_or_formula_returned,each,hig_name) + ','
            if temp[-1] == ',':
                temp = temp[:-1]
            formula +=  temp+')'
        elif golog_node.type == ':GologPicksExists':
            
            formula ='Exists('+list_args2str(golog_node.PickVars)+ '\n    '+\
                self.dump_regression_exists(predicate_args_str_or_formula_returned,golog_node.ExistsFormula,hig_name) +')'
        else:
            raise Exception("not such golog node sort:" + golog_node.type)
        return formula

    def dump_regression_universal(self,predicate_args_str_or_formula_returned,golog_node,hig_name) -> str:
        """"""
        #  predicate_formula,  every_end_s
        # golog_node.s_i , golog_node.s_o
        from GologProgramTree import Nested_list2FOLExp
        formula = ""
        predicate_args_str_or_formula_returned = predicate_args_str_or_formula_returned.replace(',s_o)',','+golog_node.s_o+')')
        predicate_args_str_or_formula_returned = predicate_args_str_or_formula_returned.replace('(s_o)','('+golog_node.s_o+')') # arm_empty(s_o)
        #'s_o'()gologself.s_o，Ors_o_1/s_o_2
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
        if golog_node.type ==':GologActTerm':
            formula ='Implies(\n    '+ actionlist2str(golog_node.ActionName,golog_node.Actionargs,golog_node.s_i)+ ',\n    '+\
                predicate_args_str_or_formula_returned+')'
            formula = self.one_step_regression_with_all_poss_ssa(formula,hig_name,golog_node.s_i)
            # hig_name
        elif golog_node.type == ':GologTest':
            andlist_str,_ = Nested_list2FOLExp().run_s(copy.deepcopy(golog_node.andlist[0]),golog_node.s_i,golog_node.s_o)# 's_o'，'s_i'
            formula = 'Implies(\n    '+ andlist_str +',\n    '+ predicate_args_str_or_formula_returned +')' 
        elif golog_node.type == ':GologSeq': # if ;then
            nested_return_formula = predicate_args_str_or_formula_returned #  on(x,y,s_o)
            for each in reversed(golog_node.GologSeqNodes):
                nested_return_formula = self.dump_regression_universal(nested_return_formula,each,hig_name)
            formula = nested_return_formula 
        elif golog_node.type == ':GologOr':
            temp = ''  + 'And(\n    '# difference!
            for each in golog_node.GologOrNodes:
                temp = temp + self.dump_regression_universal(predicate_args_str_or_formula_returned,each,hig_name) + ','
            if temp[-1] == ',':
                temp = temp[:-1]
            formula +=  temp+')'  
        elif golog_node.type == ':GologPicksExists':# difference!
            formula += 'ForAll('+list_args2str(golog_node.PickVars)+'\n    '+\
                self.dump_regression_universal(predicate_args_str_or_formula_returned,golog_node.ExistsFormula,hig_name) +')'
        else:
            raise Exception("not such golog node sort:" + golog_node.type)
        return formula

    def generate_exists_and_universal_regression_map_dict(self):
        """reverse predicate and make dict for exists/universal"""
        dict_exists = dict()
        dict_univer = dict()
        for eachactionmap in self.parser.refinementMap_actionsMap:
            for hig_name,golog_tree in eachactionmap.act_map_golog_dict.items():  
                temp_exists_ssa = dict()
                temp_univer_ssa = dict()
                for predicate,args_sort in self.parser.predicates.items(): # 
                    # for every_end_s in end_situation_list_for_SSA:# s_o_1,s_o_2,s_o
                    left_temp_exists_ssa = ''
                    left_temp_univer_ssa = ''
                    args_sort_str = ''
                    if len(args_sort) == 0:
                        # 
                        left_temp_univer_ssa = left_temp_exists_ssa = left_temp_exists_ssa +predicate+ '_('  + ')' # s_o
                    else:# >0
                        for each in args_sort: # arm_empty{},holding{'x','BlockType'}
                            if each[0] == '?':
                                # args_sort_str = args_sort_str + each + ','
                                args_sort_str = args_sort_str + each[1:] + ','# ‘?’
                        if args_sort_str[-1] == ',':
                            args_sort_str = args_sort_str[:-1] # del the last ','
                        # 
                        left_temp_univer_ssa = left_temp_exists_ssa = left_temp_exists_ssa  +predicate+ '_(' +args_sort_str + ')'# s_o
                    if args_sort_str == '':
                        golog_exists = self.dump_regression_exists(predicate+'('+args_sort_str+'s_o'+')',golog_tree,hig_name)    #  (),，'s_o'gologself.s_o
                        golog_univer = self.dump_regression_universal(predicate+'('+args_sort_str+'s_o'+')',golog_tree,hig_name) #  ()
                    else:# not zero args
                        golog_exists = self.dump_regression_exists(predicate+'('+args_sort_str+',s_o'+')',golog_tree,hig_name)    #  (),，'s_o'gologself.s_o
                        golog_univer = self.dump_regression_universal(predicate+'('+args_sort_str+',s_o'+')',golog_tree,hig_name) #  ()
                    
                    # right_temp_exists_ssa = 'And(' + golog_exists +','+ left_temp_exists_ssa + ')'# 
                    right_temp_exists_ssa = golog_exists # 6-28

                    # print(right_temp_exists_ssa)
                    right_temp_exists_ssa = self.loop_regression_with_all_poss_ssa(right_temp_exists_ssa,hig_name)
                    
                    # 's_i'
                    right_temp_exists_ssa = right_temp_exists_ssa.replace(',s_i)',')')
                    right_temp_exists_ssa = right_temp_exists_ssa.replace('(s_i)','')
                    temp_exists_ssa[left_temp_exists_ssa] = right_temp_exists_ssa
                    
                    # right_temp_univer_ssa = 'Implies(' + golog_univer +','+ left_temp_univer_ssa + ')'# 
                    right_temp_univer_ssa = golog_univer # 6-28

                    # print(right_temp_univer_ssa)
                    right_temp_univer_ssa = self.loop_regression_with_all_poss_ssa(right_temp_univer_ssa,hig_name)
                    # 's_i'
                    right_temp_univer_ssa = right_temp_univer_ssa.replace(',s_i)',')')
                    right_temp_univer_ssa = right_temp_univer_ssa.replace('(s_i)','')
                    temp_univer_ssa[left_temp_univer_ssa] = right_temp_univer_ssa
                dict_exists[hig_name] = temp_exists_ssa
                dict_univer[hig_name] = temp_univer_ssa
        json_file_exists = "./autogenerated/{0}_exists_ssa.json".format(self.domainname)
        json_file_univer = "./autogenerated/{0}_univer_ssa.json".format(self.domainname)
        with open(json_file_exists, mode='w',encoding='utf-8') as fs:
                fs.write(json.dumps(dict_exists,ensure_ascii=False,indent=1))  
        with open(json_file_univer, mode='w',encoding='utf-8') as fs:
                fs.write(json.dumps(dict_univer,ensure_ascii=False,indent=1))   
        self.dict_exists = dict_exists 
        self.dict_univer = dict_univer



# ==========================================
# test
# ==========================================

if __name__ == '__main__':
    pass

























































