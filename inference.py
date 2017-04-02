import sys
class Goal:
    def __init__(self):
        self.goals = []
        self.data = None

class Compound:
    def __init__(self):
        self.data = None
        self.predicate = None
        self.args = []
class KnowledgeBase:
    def __init__(self):
        self.implications = []
        self.facts = []

class Implication:
    def __init__(self):
        self.data = None
        self.lhs = []
        self.rhs = None

def makeCompound(clause):
    tmp = clause
    new_compound = Compound()
    new_compound.data = clause
    new_compound.predicate = tmp.split("(")[0]
    #print new_compound.predicate
    new_compound.args = tmp.split('(')[1].split(')')[0].split(',')
    #print new_compound.args
    return new_compound

def HasVariable(compound):
    for arg in compound.args:
        if arg == "x":
            return True
def Substitute(kb, compound):
    res = []
    for impl in kb.implications:
        for l in impl.lhs:
            if l.predicate == compound.predicate:
                res.append(l)
        if impl.rhs.predicate == compound.predicate:
            res.append(impl.rhs)
    for r in res:
        for i in range(len(r.args)):
            if r.args[i] == "x":
                return compound.args[i]

def Intersection(theta):
    result_theta = []
    first = theta[0]
    num = len(theta)
    for f in first:
        count = 0
        for set in theta:
            for s in set:
                if s == f:
                    count += 1
                    break
        if count == num:
            result_theta.append(f)
    return result_theta

def FetchImplications(kb, goal):
    res = []
    for impl in kb.implications:
        if impl.rhs.predicate == goal.predicate:
            if len(goal.args) > 1:
                for i in range(len(goal.args)):
                    if goal.args[i] == "x":
                        continue
                    if goal.args[i] == impl.rhs.args[i]:
                        res.append(impl)
                        break
            else:
                res.append(impl)
    return res

def FetchFacts(kb, goal):
    res = []
    for fact in kb.facts:
        if fact.rhs.predicate == goal.predicate:
            res.append(fact.rhs)
    return res

def GetVarPosition(compound):
    for i in range(len(compound.args)):
        if compound.args[i] == "x":
            return i

def BackwardChain(kb, goal, theta):
    final_theta = []
    print "Query: " + str(goal.data)
    if len(goal.lhs) > 0:
        if len(goal.lhs) == 1:
            impl = Implication()
            impl.lhs = []
            impl.rhs = goal.lhs[0]
            impl.data = goal.lhs[0].data
            final_theta = BackwardChain(kb, impl, theta)
            return final_theta
        else:
            sub_theta = []
            for lhs in goal.lhs:
                impl = Implication()
                impl.lhs = []
                impl.rhs = lhs
                impl.data = lhs.data
                sub_theta.append(BackwardChain(kb, impl, theta))
            final_theta = Intersection(sub_theta)
            return final_theta
    else:
        if theta != "" or not HasVariable(goal.rhs):
            tmp_pred = goal.rhs.predicate
            tmp_args = []
            for i in range(len(goal.rhs.args)):
                if goal.rhs.args[i] == "x":
                    tmp_args.append(theta)
                else:
                    tmp_args.append(goal.rhs.args[i])
            for fact in kb.facts:
                if fact.rhs.predicate == tmp_pred:
                    match = True
                    for i in range(len(tmp_args)):
                        if fact.rhs.args[i] != tmp_args[i]:
                            match = False
                            break
                    if match:
                        print goal.data + ": True"
                        return [theta]
        related_impl = FetchImplications(kb, goal.rhs)
        related_facts = FetchFacts(kb, goal.rhs)
        for each in related_impl:
            res = BackwardChain(kb, each, theta)
            if len(res) > 0:
                for r in res:
                    final_theta.append(r)
                break
        for each in related_facts:
            if len(each.args) == 1:
                final_theta.append(each.args[0])
            else:
                if HasVariable(goal.rhs):
                    for i in range(len(each.args)):
                        if goal.rhs.args[i] == "x":
                            continue
                        if goal.rhs.args[i] == each.args[i]:
                            final_theta.append(each.args[GetVarPosition(goal.rhs)])
    if len(final_theta) > 0:
        if theta != "":
            output_results = []
            for t in final_theta:
                if t == theta:
                    output_results.append(t)
            if len(output_results) > 0:
                print goal.data + ": True"
            else:
                print goal.data + ": False"
            return output_results
        else:
            print goal.data + ": True: ",
            theta_list = sorted(list(set(final_theta)))
            print theta_list
            return final_theta
    else:
        print goal.data + ": False"
        return final_theta

def FOLInference(kb, goal):
    if len(goal.goals) == 1:
        if HasVariable(goal.goals[0].rhs):
            BackwardChain(kb, goal.goals[0], "")
        else:
            sub = Substitute(kb, goal.goals[0].rhs)
            BackwardChain(kb, goal.goals[0], sub)
    else:
        var = False
        result = True
        theta = []

        for go in goal.goals:
            print "Query: " + str(go.data)
            if HasVariable(go.rhs):
                var = True
                theta.append(BackwardChain(kb, go, ""))
            else:
                subs = Substitute(kb, go.rhs)
                tmp_res = BackwardChain(kb, go, subs)
                if len(tmp_res) == 0:
                    result = False
            if var:
                intersect = Intersection(theta)
                if len(intersect) == 0:
                    result = False
            if result == True:
                if var:
                    print go.data + ": True: ",
                    theta_list = sorted(list(set(intersect)))
                    print theta_list
                else:
                    print go.data + ": True"
            else:
                print go.data + ": False"

def main():
    f_input = open("ip.txt", "r")
    #f_input = open(sys.argv[1], "r")
    query = Goal()
    query_line = f_input.readline().strip()
    query.data = query
    query_list = query_line.split("&")
    for q in query_list:
        query_impl = Implication()
        query_impl.data = q
        query_impl.lhs = []
        query_impl.rhs = makeCompound(q)
        query.goals.append(query_impl)
    kb = KnowledgeBase()
    kb_len = int(f_input.readline())
    for i in range(kb_len):
        impl = Implication()
        kb_line = f_input.readline().strip()
        impl.data = kb_line
        if "=>" in kb_line:
            lhs = [x for x in kb_line.split("=>")[0].split("&")]
            impl.rhs = makeCompound(kb_line.split("=>")[1])
            for part in lhs:
                impl.lhs.append(makeCompound(part))
            kb.implications.append(impl)
        else:
            impl.lhs = []
            impl.rhs = makeCompound(kb_line)
            kb.facts.append(impl)
    f_input.close()
    f_output = open("output.txt", "w+")
    sys.stdout = f_output
    FOLInference(kb, query)
    f_output.close()

if __name__ == "__main__":
    main()



