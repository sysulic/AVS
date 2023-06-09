


import codecs,os,json
def autogenerator_python_prove_file(domainname,whichStepToProve,hig_name = None,eff_fluent = None):
    """generate the python_prove*_file we want
    using "jsonfiles" and "path_of_template_py", function autogenerator_python_prove_file will generate goals of provefiles in "./autogenerated/{0}_*.py".format(domainname)
    """
    # read config
    config = {}
    # whichStepToProve = 'I','G', Preconditions of actions,effects of actions
    
    # read template file
    # "Dict for Theorems which will be proved" write into jsonfiles in "./autogenerated/domain_steps_configJSON/{0}_{1}_config.json".format(domainname,whichStepToProve). whichStepToProve = 'I','G', Preconditions of actions,effects of actions    
    if eff_fluent != None:
        json_file = "./autogenerated/domain_steps_configJSON/{0}_{1}_eff_{2}_config.json".format(domainname,hig_name,eff_fluent) #
    else:
        json_file = "./autogenerated/domain_steps_configJSON/{0}_{1}_config.json".format(domainname,whichStepToProve)   
    with codecs.open(json_file,"rb","UTF-8") as f: 
        config = json.loads(f.read())
    if not config:
        return    

    s = ""
    # path_of_template_py = "./autogenerated/domain_template/{0}_template.py".format(domainname)
    if hig_name  != None and eff_fluent == None: # 'pre' hig level action 'pickabove'/'putdown'
        path_of_template_py = r"{0}/autogenerated/domain_template/{1}_template_{2}.py".format(os.path.dirname(__file__),domainname,hig_name)
    elif hig_name != None and eff_fluent != None: # eff with eff_fluent
        path_of_template_py = r"./autogenerated/domain_template/{0}_{1}_eff_{2}_template.py".format(domainname,eff_fluent,hig_name)
    else:# hig_name == None: # for the Goal 'I'/'G' 
        path_of_template_py = "{0}/autogenerated/domain_template/{1}_{2}_template.py".format(os.path.dirname(__file__),domainname,whichStepToProve)
        # template_py_to_be_writed_G = r"{0}/autogenerated/domain_template/{1}_G_template.py".format(os.path.dirname(__file__),domainname)
        # template_py_to_be_writed_I = r"{0}/autogenerated/domain_template/{1}_I_template.py".format(os.path.dirname(__file__),domainname)
    with codecs.open(path_of_template_py, "rb", "UTF-8") as f:
        s = f.read()
    if not s:
        return
    s = s % config

    # save to file
    fn = config["file_name"]
    with codecs.open(fn, "wb", "UTF-8") as f:
        f.write(s)
        f.flush()


def copy_dir(src_path, target_path):
    if os.path.isdir(src_path) and os.path.isdir(target_path):
        filelist_src = os.listdir(src_path)
        for file in filelist_src:
            path = os.path.join(os.path.abspath(src_path), file)    
            if os.path.isdir(path):
                path1 = os.path.join(os.path.abspath(target_path), file)    
                if not os.path.exists(path1):                        
                    os.mkdir(path1)
                copy_dir(path,path1)            
            else:                                
                with open(path, 'rb') as read_stream:
                    contents = read_stream.read()
                    path1 = os.path.join(target_path, file)
                    with open(path1, 'wb') as write_stream:
                        write_stream.write(contents)
        return     True    
    else:
        return False    






def run_all_python_prove_file_in_dir_autogenerated():
    """run all python prove file in autogenerated path,like ./autogenerated/*.py"""
    copy_dir("constrainsConfig",".\\autogenerated\\constrainsConfig")
    # print("start to prove all theorem:\n")
    cur_path = os.path.dirname(os.path.realpath(__file__))
    os.putenv("PYTHONPATH", cur_path)
    case_path = os.path.join(cur_path, "autogenerated")
    lst = os.listdir(case_path)
    # print(lst)
    count_process_number = 0
    total_prove_files_count = 0
    for each in lst:
        if os.path.splitext(each)[1] == '.py':
            total_prove_files_count = total_prove_files_count + 1
    total_prove_files_count = total_prove_files_count - 1
    for c in lst:
        curr_ps = count_process_number/total_prove_files_count
        progress_width = 28
        progress_str = '{0:s}'.format(int(progress_width * curr_ps) * '>').ljust(progress_width, '-')
        # progress_str = '{0:s}'.format(int(progress_width * curr_ps) * '|~_~)').ljust(progress_width, ' ')
        msg_str = '{0:.0%}:'.format(curr_ps)
        
        if os.path.splitext(c)[1] == '.py':
            print(f'\r{progress_str} {msg_str}')#, end='')
            count_process_number += 1
            #print('py .\\autogenerated\\{0}'.format(c))
            #os.system('py .\\autogenerated\\{0}'.format(c))
            os.system('python {1}'.format(case_path,os.path.join(case_path, c)))

def delete_all_files_in_dir_autogenerated():
    cur_path = os.path.dirname(os.path.realpath(__file__))
    path = os.path.join(cur_path, "autogenerated")
    for maindir,subdir,file_name_list in os.walk(path):  
        for filename in file_name_list:  
            if(filename.endswith(".py") or filename.endswith(".json") or filename.endswith(".png") or filename.endswith(".txt")):  
                os.remove(maindir+"/"+filename)  
            else: 
                pass
    # print("all ./autogenerated/*.py have been deleted.")


if __name__ == '__main__':
    delete_all_files_in_dir_autogenerated()
    # run_all_python_prove_file_in_dir_autogenerated()









































































