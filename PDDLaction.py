import itertools

class Action:

    def __init__(self, name, parameters, positive_preconditions, negative_preconditions, add_effects, del_effects):
        self.name = name
        self.parameters = parameters
        self.positive_preconditions = positive_preconditions
        self.negative_preconditions = negative_preconditions
        self.add_effects = add_effects
        self.del_effects = del_effects

    def __str__(self):
        return 'action: ' + self.name + \
        '\n  parameters: ' + str(self.parameters) + \
        '\n  positive_preconditions: ' + str(self.positive_preconditions) + \
        '\n  negative_preconditions: ' + str(self.negative_preconditions) + \
        '\n  add_pos_effects: ' + str(self.add_effects) + \
        '\n  del_neg_effects: ' + str(self.del_effects) + '\n'

    def __eq__(self, other): 
        return self.__dict__ == other.__dict__

    def getAllAction(self, objects):
        if not self.parameters:
            yield self
            return
        types = []
        vari = []
        for var, type in self.parameters:
            types.append(objects[type])
            vari.append(var)
        for combination in itertools.product(*types):
            positive_preconditions = self.instantiate(self.positive_preconditions, vari, combination)
            negative_preconditions = self.instantiate(self.negative_preconditions, vari, combination)
            add_effects = self.instantiate(self.add_effects, vari, combination)
            del_effects = self.instantiate(self.del_effects, vari, combination)
            yield Action(self.name, combination, positive_preconditions, negative_preconditions, add_effects, del_effects)

    def instantiate(self, variList, vari, combination):
        instantiation = []
        for each in variList:
            each = list(each)
            index = 0
            for v in vari:
                while v in each:
                    each[each.index(v)] = combination[index]
                index += 1
            instantiation.append(each)
        return instantiation
