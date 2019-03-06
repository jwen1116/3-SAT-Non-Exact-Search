import random
import time
import copy

class SAT:
    def __init__(self):
        self.literals = []
        self.literalsValue = {}
        self.complementLiteralsValue = {}
        self.formula = ""
        self.tempAssignmentsLiteral = {}
        self.tempAssignmentsComplementLiteral = {}
        self.tempAssignmentsLiteralCopy = {}
        self.tempAssignmentsComplementLiteralCopy = {}
        self.numOfSatClauses = 0
        self.counter = 1
        self.dictChoice = ""
        self.zeroOccurrenceList = []
        self.numOfClauses = 0
        

    '''Generate a list of literals according to the number of literals stated by the user'''
    def LiteralListGenerator(self,numOfLiterals):
        for x in range(1,numOfLiterals + 1):
            self.literals.append("x"+str(x))
        for y in range(1, numOfLiterals + 1):
            self.literals.append("¬x"+str(y))


    '''Generate dictionaries by creating key value pair for each literal'''
    def DictKeyValueGenerator(self,numOfLiterals):
        for x in range(numOfLiterals,0,-1):
            self.literalsValue["x"+str(x)] = ""
            self.complementLiteralsValue["¬x"+str(x)] = ""


    '''Generate problem randomly according to number of clauses stated by the user'''
    def ProblemGenerator(self,numOfClauses):
        self.numOfClauses = numOfClauses
        checkList = []
        for x in range (numOfClauses):
            while True:
                temp = self.literals.copy()
                tempCheckList = []

                choice1 = random.choice(temp)
                temp.remove(choice1)
                choice2 = random.choice(temp)
                temp.remove(choice2)
                choice3 = random.choice(temp)

                if x == 0:
                    checkList.append([choice1,choice2,choice3])
                    break

                else:     
                    tempCheckList.append([choice1,choice2,choice3])
                    counter = 0

                    for item in checkList:
                        if set(item) != set(tempCheckList[0]):
                            counter += 1
                        else:
                            counter = 0
                            break
                        
                        
                    if counter > 0:
                        checkList.append([choice1,choice2,choice3])
                        break
                    
                    else:
                        continue
                        

            
            if x != 0:
                self.formula = self.formula + " ∧ "
            self.formula = self.formula + "(" + choice1 +" ∨ " + choice2 +" ∨ " + choice3 + ")"

            
        return self.formula


    '''Check the number of occurrence of each literal inside the formula'''
    def CheckOccurrence(self):
        occurrenceFormula = self.formula
        occurrenceList = []
        for i in reversed(self.literals):
            count = occurrenceFormula.count(i)
            occurrenceFormula = occurrenceFormula.replace(i,"Done")
            if count == 0:
                self.zeroOccurrenceList.append(i)
                continue
            elif count != 0:
                occurrenceList.append([i,count])

        occurrenceList.sort(key=lambda x:x[1],reverse=True)
        return occurrenceList


    '''Greedy Algorithm: Assign value to literals inside dictionaries according to occurrence'''
    def AssignValueAccordingOccurrence(self,numOfOccurrenceList):
        for i in numOfOccurrenceList:
            if self.literalsValue.get(i[0]) == "" or self.complementLiteralsValue.get(i[0]) == "":
                if "¬" in i[0]:
                    self.complementLiteralsValue[i[0]] = 1
                    self.literalsValue[i[0][1:]] = 0
                else:
                    self.literalsValue[i[0]] = 1
                    self.complementLiteralsValue["¬"+i[0]] = 0


    '''Algorithm to search for better result: Randomly decide the number of changes, literals and dictionary. Value of literals selected will be changed accordingly inside the selected dictionary.'''
    def AssignValueNeighbour(self,numOfOccurrenceList,position):
        numOfChanges = random.randint(2,9)
        availableDict = ["currentAssignment","closestAssignment"]
        self.dictChoice = random.choice(availableDict)
        self.tempAssignmentsLiteralCopy = copy.deepcopy(self.tempAssignmentsLiteral)
        self.tempAssignmentsComplementLiteralCopy = copy.deepcopy(self.tempAssignmentsComplementLiteral)
        tempList = self.literals.copy()
        if len(self.zeroOccurrenceList) != 0:
            for item in self.zeroOccurrenceList:
                tempList.remove(item)
        selectedLiterals = []
        
        for i in range(numOfChanges):
            choice = random.choice(tempList)
            selectedLiterals.append(choice)

            if "¬" in choice:    
                tempList.remove(choice)
                if choice[1:] in tempList:
                    tempList.remove(choice[1:])
            else:
                tempList.remove(choice)
                if "¬"+choice in tempList:
                    tempList.remove("¬"+choice)

            
        for item in selectedLiterals:
            if self.dictChoice == "currentAssignment":
                if "¬" in item:
                    if self.complementLiteralsValue.get(item) == 1:
                        self.complementLiteralsValue[item] = 0
                        self.literalsValue[item[1:]] = 1
                    else:
                        self.complementLiteralsValue[item] = 1
                        self.literalsValue[item[1:]] = 0
                else:
                    if self.literalsValue.get(item) == 1:
                        self.literalsValue[item] = 0
                        self.complementLiteralsValue["¬"+item] = 1
                    else:
                        self.literalsValue[item] = 1
                        self.complementLiteralsValue["¬"+item] = 0
                        
            elif self.dictChoice == "closestAssignment":
                if "¬" in item:
                    if self.tempAssignmentsComplementLiteralCopy.get(item) == 1:
                        self.tempAssignmentsComplementLiteralCopy[item] = 0
                        self.tempAssignmentsLiteralCopy[item[1:]] = 1
                    else:
                        self.tempAssignmentsComplementLiteralCopy[item] = 1
                        self.tempAssignmentsLiteralCopy[item[1:]] = 0
                else:
                    if self.tempAssignmentsLiteralCopy.get(item) == 1:
                        self.tempAssignmentsLiteralCopy[item] = 0
                        self.tempAssignmentsComplementLiteralCopy["¬"+item] = 1
                    else:
                        self.tempAssignmentsLiteralCopy[item] = 1
                        self.tempAssignmentsComplementLiteralCopy["¬"+item] = 0
           
                
    
    '''Substitute the boolean value of each literal into the formula'''
    def AssignValueFormula(self):
        newFormulaWithAssignment = self.formula
        self.counter += 1

        if self.dictChoice == "currentAssignment" or self.dictChoice == "":
            for key in self.complementLiteralsValue:
                newFormulaWithAssignment = newFormulaWithAssignment.replace(key,str(self.complementLiteralsValue[key]))
            for key in self.literalsValue:
                newFormulaWithAssignment = newFormulaWithAssignment.replace(key,str(self.literalsValue[key]))
        else:
            for key in self.tempAssignmentsComplementLiteralCopy:
                newFormulaWithAssignment = newFormulaWithAssignment.replace(key,str(self.tempAssignmentsComplementLiteralCopy[key]))
            for key in self.tempAssignmentsLiteralCopy:
                newFormulaWithAssignment = newFormulaWithAssignment.replace(key,str(self.tempAssignmentsLiteralCopy[key]))


        return newFormulaWithAssignment


    '''Check each of the clauses to get true or false value'''
    def CheckClauses(self,newFormula):
        stringLength = len(self.formula)
        newClauseFormula = ""
        
        for i in range (0,stringLength,14):
            
            if newFormula[i:i+11] != "":
                if i != 0:
                    newClauseFormula += " ∧ "
                if "1" in newFormula[i:i+11]:
                    newClauseFormula += "1"
                else:
                    newClauseFormula += "0"
                
        return newClauseFormula

    
    '''Check the entire formula to to determine whether a solution is found'''
    def CheckProblem(self,clauseFormula):
        if "0" in clauseFormula:
            numOf1 = clauseFormula.count("1")
            if numOf1 > self.numOfSatClauses:
                self.numOfSatClauses = numOf1
                if self.dictChoice == "" or self.dictChoice == "currentAssignment":
                    self.tempAssignmentsLiteral = copy.deepcopy(self.literalsValue)
                    self.tempAssignmentsComplementLiteral = copy.deepcopy(self.complementLiteralsValue)
                elif self.dictChoice == "closestAssignment":
                    self.tempAssignmentsLiteral = copy.deepcopy(self.tempAssignmentsLiteralCopy)
                    self.tempAssignmentsComplementLiteral = copy.deepcopy(self.tempAssignmentsComplementLiteralCopy)
            if self.counter == 50:
                self.PrintMostSatisfiableAssignments()
            return 0
            
        else:
            self.numOfSatClauses = self.numOfClauses
            if self.dictChoice == "" or self.dictChoice == "currentAssignment":
                self.tempAssignmentsLiteral = copy.deepcopy(self.literalsValue)
                self.tempAssignmentsComplementLiteral = copy.deepcopy(self.complementLiteralsValue)
            elif self.dictChoice == "closestAssignment":
                self.tempAssignmentsLiteral = copy.deepcopy(self.tempAssignmentsLiteralCopy)
                self.tempAssignmentsComplementLiteral = copy.deepcopy(self.tempAssignmentsComplementLiteralCopy)
            print("There is/are solution(s) for this 3-SAT problem.")
            self.PrintMostSatisfiableAssignments()
            return 1


    '''Print out the most satisfied result'''
    def PrintMostSatisfiableAssignments(self):
        '''print("\nThe most satisfied assignments for this 3-SAT problem are:")
        print("=======================")
        print("Literal\t\tValue")
        print("=======================")
        for i in self.tempAssignmentsLiteral:
            print("{}\t\t{}".format(i,self.tempAssignmentsLiteral[i]))
        for i1 in self.tempAssignmentsComplementLiteral:
            print("{}\t\t{}".format(i1,self.tempAssignmentsComplementLiteral[i1]))
        print("=======================")'''
        print("The best it can hit is ",self.numOfSatClauses,"/",self.numOfClauses,"clauses.")
   


       

if __name__ == '__main__':
    a = SAT()
    counter = 1
    checkResult = 3
    start = time.time()
    _input = 15

    a.LiteralListGenerator(_input)
    a.DictKeyValueGenerator(_input)
    
    print("Problem Generation: " + a.ProblemGenerator(30) + "\n")
    o = a.CheckOccurrence()
    print("Checking for the most satisfied assignment...\n")
    
    while counter < 50 and checkResult != 1:
        if counter == 1:
            a.AssignValueAccordingOccurrence(o)
        
        else:
            a.AssignValueNeighbour(o,counter)
        
        
        b = a.CheckClauses(a.AssignValueFormula())
        checkResult = a.CheckProblem(b)
        counter += 1
        


        
    end = time.time()
    print("\nTotal Computing time: ",end-start,"s")


