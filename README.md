Main Page {#mainpage}
=========

[TOC]

---

```latex
@inproceedings{ijcai2023p351,
  title     = {Automatic Verification for Soundness of Bounded QNP Abstractions for Generalized Planning},
  author    = {Cui, Zhenhe and Kuang, Weidu and Liu, Yongmei},
  booktitle = {Proceedings of the Thirty-Second International Joint Conference on
               Artificial Intelligence, {IJCAI-23}},
  publisher = {International Joint Conferences on Artificial Intelligence Organization},
  editor    = {Edith Elkind},
  pages     = {3149--3157},
  year      = {2023},
  month     = {8},
  note      = {Main Track},
  doi       = {10.24963/ijcai.2023/351},
  url       = {https://doi.org/10.24963/ijcai.2023/351},
}
```
# Automatic-Verification-for-Soundness-of-Bounded-QNP-Abstractions-for-Generalized-Planning

Please read the [online document here](https://sysulic.github.io/AVS/).

Installation dependencies:

```bash
pip install z3 z3-solver==4.8.10.0 networkx func_timeout matplotlib 
```

Based on python3.8, this tool automatically verifies whether high-level modeling is a "sound abstraction" corresponding to low-level models. 
Some windows users may need the following installation scripts if they are not using miniconda:

```bash
python -m pip install z3 z3-solver==4.8.10.0 networkx func_timeout matplotlib 
```

Parameters:

```bash
> python main.py --help
usage: main.py [-h] [-domainname DOMAINNAME] [-DEBUG DEBUG] [-timeout_number TIMEOUT_NUMBER]

hig-low sound abstraction prove.

optional arguments:
  -h, --help            show this help message and exit
  -domainname DOMAINNAME
                        domainname for qnp/pddl/refinementmap/constraint files -- OPTIONAL FOR TEST
  -DEBUG DEBUG          print DEBUG message or not -- OPTIONAL FOR TEST
  -timeout_number TIMEOUT_NUMBER
                        the autogenerated prove file wait for timeout_number(s),if timeout,it will return unknown message and then please open the file and add some  
                        Necessary constraint message. -- OPTIONAL FOR TEST
```

The default parameter equivalent call:

```bash
python main.py 
python main.py -domainname "blocks_clear" -DEBUG False -timeout_number 3.1415926
```

take gripper for example:

```bash
python main.py -domainname "gripper" -DEBUG True -timeout_number 10 
```

![.\output.gif](https://github.com/sysulic/Automatic-Verification-for-Soundness-of-Bounded-QNP-Abstractions-for-Generalized-Planning/blob/main/output.gif?raw=true)

## System function introduction

- Input: Two pddl files of the low-level STRIPS model, placed in the example folder + high-level QNP file + refined mapping files from high-level to low-level programs. 

- Output: Determine whether the high-level is the "sound abstraction" corresponding to the low-level program.

- Program input:

Although you only need to pass in `domainname ='block_clear'` (denoted by `{domainname}` below}) for convenience, each certification task requires the user to provide four corresponding location files by hand, and the files need to meet the following naming conventions:

1. “`./examples/{domainname}/{domainname}\_d.txt`“Use STRIPS modeling to write a low-level problem domain description file in pddl format, and "`./examples/{domainname}/{domainname}\_p.txt`"Problem description file for low-level problems (expanded keywords to adapt to Golog program input).

2. “`./examples/{domainname}/{domainname}.qnp`“QNP format refers to the format proposed by `qnp2fond` .

3. “`./refinementMap/{domainname}/{domainname}_RefinementMap.txt`” refinment mapping files.

4. “`./constrainsConfig/{domainname }_constrain.txt`“The background knowledge and common sense axioms known by the computer need to be provided in the proof process, that is, the text file of the domain-specific constraint axiom set, and the format can refer to the z3 logic formula writing specification. 
   Temporary variables such as z and w that only appear here need to be declared in the file before they are used.
- Final output file：

All the files below `autogenerated` are automatically generated. The `*.py` file is the automatically generated specific theorem file that meets the z3-solver format, and the others are auxiliary files, including:

Under the `constrainsConfig` folder is the domain constraint `domain constrain` file, `domain_steps_configJSON` is the relevant certification formula dictionary, and under the `domain_template` is the automatically generated `python` certification file template. 
All `json` related configuration information can refer to the corresponding file name, and the generated png image is the `scenario-action-parameters` migration diagram of the low-level `Golog` program corresponding to the high-level action of the corresponding name.

## Catalog Introduction

Folders

```cmd
autogenerated # The *.py file under autogenerated automatically generated is the "certification file" corresponding to the certification subtask, here is the target file, and then
constrainsConfig # Configure the state constraint formula of a specific proof domain here. If the file is empty, it means that there is no constraint
examples # Store the pddl input file of STRIPS and the qnp input file of QNP
refinementMap #Store refinement mapping function input file
```

Files

```python
main.py # main program entry

PDDLaction.py # Low-level action class, used in refinementMapParser.py to store low-level STRIPS action information

QNPparser.py # parser that reads qnp files

refinementMapParser.py # The parser of the pddl file and the parser of the refinement mapping file, called here

GologProgramTree.py # In the refined mapping, a high-level action ==> a low-level Golog program tree

Regression.py # All functions related to regression, including "single-step regression/circular regression to program input scenario s_i/extended existence regression/extended arbitrary regression"

topologicalSort.py # The scene change arrow is reversed, and then the topological sorting is used to get the cyclic regression scene change order ssa is "left node.s_output" replaced with "right node.s_input"

utils.py # Tool functions are here, including delete_all_files_in_dir_autogenerated run_all_python_prove_file_in_dir_autogenerated and other tool functions

requirements.txt

README.md
```

## The Main Process

1. “`Dict for Theorems which will be proved`“ write into JSON files in “`./autogenerated/domain_steps_configJSON/{0}_{1}_config.json`“.format(domainname,whichStepToProve). whichStepToProve = 'I','G', Preconditions of actions,effects of actions
2. “`path_of_template_py` = `./autogenerated/domain_template/{0}_template.py`“.format(domainname)`
3. using “`JSON files`“ and “`path_of_template_py`“, function  “`autogenerator_python_prove_file`“  will generate goals of prove files in “`./autogenerated/{0}_*.py.format(domainname)`“

The core processing logic generates the `json` file in the first step：

> JSON is based on "`prove_tasks_list`" to prove the task list, such as `['I','G','pickabove_pre','pickabove_eff','putaside_pre','putaside_eff']`, respectively processing the corresponding proof tasks to get the corresponding 

The low-level language logic formula that needs to be proved in the `json` configuration file contains the corresponding high-level language logic formula.

The processing conversion of the low-level `Golog` program is the second core logic.

## Important Class and Function description

### Main Function

```python
main.py # The outline of the detailed calculation and generation process of the entry main program
"""
    main process:
    1. "Dict for Theorems which will be proved" write into jsonfiles in "./autogenerated/domain_steps_configJSON/{0}_{1}_config.json".format(domainname,whichStepToProve). whichStepToProve = 'I','G', Preconditions of actions,effects of actions will "Automatically generate formulas that need to be proved and configure them in the json file".
    2. path_of_template_py = "./autogenerated/domain_template/{0}_template.py".format(domainname)---Automatically generate the template file used when generating the python certification file in z3-solver format
    3. using "jsonfiles" and "path_of_template_py", function autogenerator_python_prove_file will generate goals of provefiles in "./autogenerated/{0}_*.py".format(domainname)---Generate and run the python certification file corresponding to the z3-solver format.
"""
    # delete all files in dir autogenerated before
    ......# Omit the specific implementation follow-up explanation here, the same below
    # PDDL parser
    ......
    # RefinementMap parser
    ......
    # QNP parser
    ......
    # Refinement Map process
    ......
    # Regression
    ......
    # write template py
    ......
    # generate the correct "low theorem" --> "hig theorem" and write goals out into json config files "./autogenerated/domain_steps_configJSON/{0}_{1}_config.json"
    # steps of how to map hig level description into low level golog FOL formula and prove:
    # 1. I
    # 2. G
    # 3. pres of actions
    # 4. effs of actions
    ......
    # generate the python_prove*_file we want 
    # with "./midfile/{domainname}_*I/G_config.json" and "{domainnaoe}_template.py"
    ......
    # generate the python_prove*_file we want 
    # with "./midfile/{domainname}_*Pre/Eff_config.json" and "{domainnaoe}_template.py"
    ......
    # run_all_python_prove_file_in_dir_autogenerated    
```

`parser`Read qnp file / pddl file of STRIPS:

```python
QNPparser.py # parser that reads qnp files
PDDLaction.py # Low-level action class, used in refinementMapParser.py to store low-level STRIPS action information
```

### Parsers

#### QNPparser

Member variables stored by `qnp_action`:

```python
class qnp_action:
    def __init__(self,actionnameline,prelist,efflist,all_variables,all_fluents) -> None:
self.name = actionnameline # High-level action name      
self.prestate = {}# High-level action pre premise      
self.effstate = {}# High-level action eff effect
```

`QNP_Parser`Stores member variables：

```python
class QNP_Parser:  
def __init__(self,qnpfile) -> None:       
self.name = "" # name       
self.initstate = {} # Initial state       
self.goalstate = {} # Goal state       
self.stateRepresentation_variables = [] # State represents numeric variables       
self.stateRepresentation_fluents = [] # State representation logic Boolean variable
```

#### ReinfinementMapParser.py

```python
refinementMapParser.py # The parser of the pddl file and the parser of the refinement mapping file, called here
GologProgramTree.py # In the refined mapping, a high-level action ==> a low-level Golog program tree
```

This file includes the parser of the pddl file of the STRIPS model and the refinementmap file. The low-level action object class of the pddl used is in ``:

```python
class Action:

    def __init__(self, name, parameters, positive_preconditions, negative_preconditions, add_effects, del_effects):
        self.name = name             # 
        self.parameters = parameters # 
        self.positive_preconditions = positive_preconditions # 
        self.negative_preconditions = negative_preconditions # 
        self.add_effects = add_effects # 
        self.del_effects = del_effects # 
```

### Regression Classes

```python
Regression.py # All functions related to regression, including "single-step regression/cyclic regression to program input scenario s_i/extended existence regression/extended arbitrary regression". 
Topological sorting is used to reverse the scene change arrow, and then topological sorting is used to get the cyclic regression scene change order ssa is "left node.s_output" replaced with "right node.s_input".
def __init__#Specific initialization parameter input (self, domainname input problem-related name, STRIPS model object read by parserinput, QNP object read by qnp_parser, reverse_eachgolog_set_of_s_io_order_list records the context transformation relationship between high-level motion and low-level Golog program, reverse_situation_tree scenario migration tree, 
eachgolog_set_of_s_act scenario-action set, each_situation_action_args scenario-action-action parameter dictionary) -> None:

# regression function initialization constructor input parameter analysis:
```

The functions of these functions are:

```python
def get_poss(self,act):
"""Get poss"""
def generate_poss_file(self):  
"""Write a file of the number of high-level jobs, including Poss axioms in any possible context of each action"""
def one_step_poss_regression(self,test_phi_formula,lowaction,domainname,hig_action_name,s_i):# action is'low level action name'
"""one_step_poss_regression"""
def get_ssa(self): 
"""Get low-level specific state transition ssa dictionary"""
def generate_ssa_file(self):
def one_step_ssa_regression(self,test_psi_formula,predicate,domainname,hig_action_name,s_i):   
"""one_step_ssa_regression given'predicate' and'formula'"""
```

The main regression functions include:

```python
# the main Regression function entrances:
def one_step_regression_with_all_poss_ssa(self,test_formula,hig_action_name,s_i):
    """Input a formula,return the formula after one_step_regression_with_all_poss_ssa"""
    # 1. \mathcal{D}_{poss}:for all action one_step_poss_regression
    # 2. \mathcal{D}_{ssa}:for all predicates one_step_ssa_regression
    # 3. \mathcal{D}_{una}:do not simplify here but wait for output get it simplied by z3-solver to cancel the nested duplicated terms.
def loop_regression_with_all_poss_ssa(self,test_formula,hig_action_name):
    """Input a formula,return the formula after loop multiple_steps_regression_with_all_poss_ssa"""
def dump_regression_exists(self,predicate_args_str_or_formula_returned,golog_node,hig_name) -> str:
        """Existentially Extended regression"""    
def dump_regression_universal(self,predicate_args_str_or_formula_returned,golog_node,hig_name) -> str:
    """Universally Extended regression"""
# Predicate formula predicate_formula, the ending scenario of the predicate after the action in the predicate formula is completed every_end_s
# Distinguish golog_node.s_i, golog_node.s_o under specific actions
def generate_exists_and_universal_regression_map_dict(self): 
"""reverse predicate and make dict for exists/universal"""
def generate_exists_and_universal_regression_map_dict(self): 
"""Generate all predicate and make dict for exists/universal """
```
