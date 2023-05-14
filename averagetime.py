import os
def run_average_time():
    """run time"""
    alltimes = list()
    tasks = ["blocks_clear","gripper","onAB","logistic","getlast","findA","corner"]
    for task in tasks:
        import time
        average = 0
        sum = 0
        for i in range(0,1):#range(0,100):
            start_time = time.perf_counter()
            os.system('python main.py -domainname  {0}'.format(task))
            end_time = time.perf_counter()
            diff = end_time - start_time
            average = average*i/(i+1) + diff/(i+1)
            sum += diff
        print('-'*30)
        print('{0} average-cost is: '.format(task),average,'(s).')
        print(sum/100)
        alltimes.append(task)
        alltimes.append(str(average)+'s')
    print("\n"*5 )
    print(alltimes)


if __name__ == '__main__':
    run_average_time()








































































