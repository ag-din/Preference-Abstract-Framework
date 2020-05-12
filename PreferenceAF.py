#!/usr/bin/env python
# -*- coding: utf-8 -*-

import itertools

##################################################################################
### PREFERENCE BASED ABSTRACT ARGUMENTATION FRAMEWORK - Amgoud and Cayrol (2002)
##################################################################################

# A preference-based argumentation framework (PAF) is a triplet <A, R, Pref>,
# where Pref is a (partial or total) preordering on A × A. We recall
#that >>_{Pref} denotes the associated strict partial ordering.

# >>_{Pref} denotes the associated strict partial ordering
# Si A >>_{Pref} B, A es estrictamente preferido a B.


# NOTA: Dados 2 argumentos A y B:
# A >= B: A es al menos tan preferido como B
# A > B: A es estrictamente preferido a B
# A ~~ B: A >= B y B>= A
# A ~ B: A y B no son comparables (ni A>=B ni B>=A)

#  >= is a pre-order on X iff  >=  is reflexive (x  >=  x) and transitive (if x  >=  y and y  >=  z then
#x   >= z)
 
##########
### suposición parcial or complete preorder
### Pref = [([d], [a,c], [b])] (>>, ~~)  --> a~~c, d>>b, a>>b, c>>b
#########

class PAF:
    def __init__(self, arguments, relations, preferences):
        self.arguments = arguments
        self.relations = relations
        self.preferences = preferences
        self.relationsPAF = PAF.relationsPaf(self)
        self.semantics = PAF.Semantics(self)
        self.argumentClass = PAF.ArgumentClass(self)

        # True si Pref es un preordenamiento completo (todo par de args en argumentos)
        # es comparable, sino False

    # checheo que los args en Pref estén todos en arguments, sino false

    def argInPref(self, arg):
         if len(self.preferences)>0 and len(self.arguments)>0 and arg in self.arguments:
            for tpl in self.preferences:
                for lst in tpl:
                    if arg in lst:
                        return True 
            return False
         else:
            return None



    def allArgumentsInPref(self):
        if len(self.preferences)>0 and len(self.arguments)>0:
            prefArgs = set()
            for tpl in self.preferences:
                for lst in tpl:
                    for e in lst:
                        prefArgs.add(e)
            if len(prefArgs.intersection(self.arguments)) == len(self.arguments) and len(prefArgs) == len(self.arguments):
                return True
            else:
                return False
        else:
            return None

    def is_completePref(self):
        if len(self.preferences) == 1 and self.allArgumentsInPref() == True:
            return True
        else:
            return False


    def comparePref(self, arg1, arg2):
        lst = []
        if arg1 in self.arguments and arg2 in self.arguments:
            if self.is_completePref() == True:
                tpl = self.preferences[0]
                for e in tpl:
                    if arg1 in e and arg2 not in e:
                        lst.append(arg1)
                    if arg1 not in e and arg2 in e:
                        lst.append(arg2)
                    if arg1 in e and arg2 in e:
                        lst.append("equal")
                if len(lst) == 1 and lst[0] == "equal":
                    return "equal"
                else:
                    return lst[0]
            else:
                if self.allArgumentsInPref() == True: ## estan todos pero no todos son cmparables
                    for tpl in self.preferences:
                        for ls in tpl:
                            if arg1 in ls and arg2 in ls:
                                return "equal"
                            if arg1 in ls and arg2 not in ls:
                                lst.append(arg1)
                            if arg2 in ls and arg1 not in ls:
                                lst.append(arg2)
                        if len(lst) > 0 and len(lst) != 2:
                            return "incomparable"
                        if len(lst) == 2:
                            return lst[0]
                        
                else:
                    if self.argInPref(arg1) == True and self.argInPref(arg2) == True:
                        for tpl in self.preferences:
                            for ls in tpl:
                                if arg1 in ls and arg2 in ls:
                                    return "equal"
                                if arg1 in ls and arg2 not in ls:
                                    lst.append(arg1)
                                if arg2 in ls and arg1 not in ls:
                                    lst.append(arg2)
                            if len(lst) > 0 and len(lst) != 2:
                                return "incomparable"
                            if len(lst) == 2:
                                return lst[0]

                    else:
                        return None 
            
# Let A, B be two arguments such that B R A. A defends itself 
#against B iff A Pref B.

    # Dado un PAF retorna True si existe al menos un argumento en PAF 
    # que ataca a arg en el sentido de PAF sino retorna False. Retorna
    # None si arg no existe en AF.
    def is_attackedPAF(self, arg):
        #status = False
        if arg in self.arguments:
            for x in self.relations:
                if x[1] == arg:
                    if self.comparePref(x[1], x[0]) == x[0]:
                        return True
            return False
        else:
            return None

    # Dado un argumento "arg" y el PAF
    # retorno una lista de argumentos que atacan a "arg" en el sentido de PAF. Retorna
    # None si arg no existe en AF.
    def get_arg_attackers(self, arg):
        if arg in self.arguments:
            attackers = []
            for i in self.relations:
                if i[1] == arg:
                    if self.comparePref(i[1], i[0]) == i[0]:
                        attackers.append(i[0])
            return set(attackers)
        else:
            return None

    def relationsPaf(self):
        relPAF = set()
        for e in self.arguments:
            setAttackers = self.get_arg_attackers(e)
            for a in setAttackers:
                relPAF.add((a, e))
        return relPAF

    # Dado un conjunto de argumentos X y las relaciones de ataque retorno
    # el conjunto de argumentos a los X ataca.  Retorna
    # None si hay almenos un argumento en set_of_args que no existe en AF.
    def get_attacked_args(self, set_of_args):
        if len(set_of_args.intersection(self.arguments)) == len(set_of_args):
            attacked = set()
            for arg in set_of_args:
                for i in self.relationsPAF:
                    if i[0] == arg:
                        attacked.add(i[1])
            return attacked
        else:
            return None

    def powerset(self, iterable):
        s = list(iterable)
        return set(itertools.chain.from_iterable(itertools.combinations(s, r) for r in range(len(s)+1)))

    # Computa los conjuntos de argumentos que son cfs (subconjuntos de argumentos
    # que no se atacan entre sí).
    def compute_cfs(self):
        pwr = self.powerset(self.arguments)
        if len(self.relationsPAF) > 0 and len(self.arguments) > 0:
            for x in self.relationsPAF:
               x1 = x[0]
               x2 = x[1]
               todelete = []
               for i in pwr:
                   if (x1 in i) and (x2 in i):
                       todelete.append(i)
               for i in todelete:
                   pwr.remove(i)
        return set(pwr)

    # An argument arg in A is ACCEPTABLE with respect to E (subconjunto de A) if and only if 
    # E defends arg, that is, forall b in A such that (b,arg) in RPaf, exists c in E
    # such that (c,b) in RPaf.
    def compute_acceptability(self, arg, E):
        if arg in self.arguments:
            if len(set(E).intersection(self.arguments)) == len(set(E)):
                attackers = self.get_arg_attackers(arg)
                if (attackers != None and len(E)>0):
                    atks = []
                    
                    for y in attackers: # recorro attackers de arg
                        yStatus = False
                        yAtackers = self.get_arg_attackers(y) # obtengo atackers de y
                        if len(yAtackers.intersection(E)) > 0: # interseccion entre E e yAtackers no vacía
                            yStatus = True # al menos un elemento de E ataca al elemento y que ataca a un argumento arg
                        atks.append(yStatus)
                    
                    if all(atks): # arg es aceptable respcto a E (todos sus atackers son atacados por elementos de E)
                        return True
                    else:
                        return False
                else:
                    return False
            else:
                None
        else:
            return None

    # Checkeo que los argumentos especificados en las relaciones de ataque existan en A
    def checkArgumentsInRelations(self):
        if len(self.arguments) > 0:
            if len(self.relationsPAF) > 0:
                for x in self.relationsPAF:
                    lst = []
                    status = True
                    if x[0] not in self.arguments or x[1] not in self.arguments:
                        status = False
                    lst.append(status)   
                    if all(lst):
                        return True
                    else:
                        return False
            else:
                return False
        else:
            return False


    class ArgumentClass:

        def __init__(self, paf):
            self.paf = paf
        #The class of acceptable arguments, denoted by AccR {A ∈ A | ∀B ∈ A if B R A then A >> Pref B}
        def arg_acceptable_class(self):
            accClass = []
            if self.paf.checkArgumentsInRelations()==True:
                if len(self.paf.arguments) > 0 and len(self.paf.relationsPAF) > 0:
                    for x in self.paf.arguments:
                        xAttackers = self.paf.get_arg_attackers(x)
                        if len(xAttackers) == 0:
                            accClass.append(x)
            return set(accClass)

        #The class of rejected arguments is
        #denoted by RejR = {A ∈ A | ∃B ∈ Acc R ,Pref s.t. B R A and not (A >> Pref B)}
        def arg_rejected_class(self):
            rejClass = []
            if self.paf.checkArgumentsInRelations()==True:
                if len(self.paf.arguments) > 0 and len(self.paf.relationsPAF) > 0:
                    for x in self.paf.arguments:
                        xAttackers = self.paf.get_arg_attackers(x)
                        if len(xAttackers.intersection(self.paf.argumentClass.arg_acceptable_class())) > 0:
                            rejClass.append(x)
            return set(rejClass)

        # The class of arguments in abeyance is AbR = A\(AccR ∪ RejR).
        def arg_abeyance_class(self):
            abyClass = []
            if self.paf.checkArgumentsInRelations()==True:
                unAccRRejR = self.paf.argumentClass.arg_acceptable_class().union(self.paf.argumentClass.arg_rejected_class())
                abyClass = self.paf.arguments.difference(unAccRRejR)
            return set(abyClass)

    def compute_admissibility(self, cfs):
        if self.checkArgumentsInRelations()==True:
            if len(cfs) > 0:
                admissible = []
                # tomo cada cf subset de cfs del AF
                for cfset in cfs:
                        attackers = set()
                        # voy arg a arg de ese cf subset
                        for cfsetmember in cfset:
                            # obtengo conjunto de args (externos al cf subset) que atacan a args del cf subset
                            attackers = attackers.union(self.get_arg_attackers(cfsetmember))

                        attackedbycfsmembers = []
                        # recorro cada arg dentro del conjunto de args (externos al cf subset) que atacan a elementos del cf subset
                        for attacker in attackers:
                            atk = False
                            # obtengo args que atacan a los atacadores de miembros del cf subset
                            attackedby = self.get_arg_attackers(attacker)
                            # recorro cada arg dentro del cf subset
                            for cfsetmember in cfset:
                                # True si existe al menos un elemento del cf subset que ataca a un argumento que ataca a un miembro del cf subset
                                if cfsetmember in attackedby:
                                    atk = True
                            # añado True o False
                            attackedbycfsmembers.append(atk)
                        # Si todos son True añado cf subset como conjunto cf admisible
                        if all(attackedbycfsmembers):
                            admissible.append(cfset)
                return set(admissible)
            else:
                return set()
        else:
            return None

    ### Acceptability Semantics (Stable, Grounded, Preferred, Complete)
    # E is a stable extension of AF only if it is a conflict-free set that attacks 
    # every argument that does not belong in E (formally, forall a in A\E, exists
    # b in E forall a in A\E,exists b in E such that (b,a) in R(b,a) in R.
    class Semantics:
        def __init__(self, af):
            self.af = af
            self.status = AF.Semantics.argumentStatus(self.af)

        def compute_stable_extensions(self):
            if self.af.checkArgumentsInRelations()==True:
                adm = self.af.compute_cfs()
                stb = []
                if len(adm)>0:
                    for x in adm:
                         if set(x).union(self.af.get_attacked_args(set(x))) == self.af.arguments:
                            stb.append(x)
                return set(stb)
            else:
                return None

    # E is the (unique) grounded extension of AF only if it is the smallest element   
    # (with respect to set inclusion) among the complete extensions of S.
        def compute_grounded_extensions(self):
            if self.af.checkArgumentsInRelations()==True:
                grd = []
                compExt = self.af.semantics.compute_complete_extensions()
                
                count=0
                l = -99
                if len(compExt)>0:
                    for conj in compExt:
                        if count == 0:
                            l = len(conj)
                        else:
                            if len(conj) < l:
                                l = len(conj)
                        count+=1
                    
                    for x in compExt:
                        if len(x) == l:
                            grd.append(x)

                return set(grd)
            else:
                return None


    #def compute_grounded_extension(adm, relations, arguments):
    #    grd = []
    #    rel = list(relations)
    #    attackedbyin = []
    #    someArg = True

    #    if len(adm) == 1:
    #        return set(grd)

    #    for x in arguments:
    #            if is_attacked(x, rel) != True:
    #                if x not in grd:
    #                    grd.append(x)   # lista de arg atacados

    #    if len(grd) == 0:
    #        return set(grd)

    #    while someArg:
    #        for x in grd:
    #            if len(framework[x]) <= 1:
    #                attackedbyin.append(framework[x])
    #            else :
    #                attackedbyin.extend(framework[x])

    #        for r in rel:
    #            for atk in attackedbyin:
    #                if r[0]== atk:
    #                    rel.remove(r)

    #        for i in arguments:
    #            if is_attacked(i, rel) != True:
    #                if i not in grd:
    #                    grd.append(i)
    #                else:
    #                    someArg = False

    #    return set(grd)



    # E is a preferred extension of AF only if it is a maximal element
    # (with respect to the set-theoretical inclusion) among the admissible sets
    # with respect to AF.
        def compute_preferred_extensions(self):
            if self.af.checkArgumentsInRelations()==True:
                pref = []
                cfs = self.af.compute_cfs()
                if len(cfs)>0:
                    adm = self.af.compute_admissibility(cfs)
                    if len(adm)>0:
                        maxLen = 0
                        ## busco el conjunto admisible más grande
                        for i in adm:
                            if len(i)>maxLen:
                                maxLen = len(i)
                        ## busco el conjunto admisible con número de elementos == maxLen
                        for i in adm:
                            if len(i)==maxLen:
                                pref.append(i)

                return set(pref)
            else:
                return None

    #def compute_complete_extensions(adm):
    #    grd = compute_grounded_extension(adm, relations, arguments)
    #    prf = compute_preferred_extensions(adm)

    #    grd2 = str(grd).replace("'",'')
    #    prf2 = str(prf).replace('(','').replace(',','').replace(')','').replace("'",'')


    #    if prf2 == grd2:
    #        return prf2
    #    else:
    #        return grd2+" "+prf2


    # An admissible set S of arguments is called a complete extension iff
    # each argument, which is acceptable with respect to S, belongs to S.
        def compute_complete_extensions(self):
            if self.af.checkArgumentsInRelations()==True:
                compl = []
                cfs = self.af.compute_cfs()
                if len(cfs)>0:
                    adm = self.af.compute_admissibility(cfs)
                    if len(adm)>0:
                        for conj in adm:
                            accArgs = set()
                            for x in self.af.arguments:
                                if self.af.compute_acceptability(x, conj) == True:
                                    accArgs.add(x)
                            if len(accArgs.intersection(conj)) == len(accArgs) and len(accArgs.intersection(conj)) == len(conj):
                                lst = []
                                for x in accArgs:
                                    s = False
                                    if x in conj:
                                        s = True
                                    lst.append(s)
                                if all(lst):
                                    compl.append(conj)
                return set(compl)
            else:
                return None

        class argumentStatus:
            def __init__(self, af):
                self.af = af
                #self.semantics = set()
            
            def skepticallyAccepted(self, sem):
                accepted = set()
                if len(sem) > 0:
                    for a in self.af.arguments:
                        lst = []
                        for extension in sem:
                            if a in extension:
                                lst.append(True)
                            else:
                                lst.append(False)
                        if all(lst):
                            accepted.add(a)
                return accepted

            def credulouslyAccepted(self, sem):
                accepted = set()
                if len(sem) > 0:
                    for a in self.af.arguments:
                        lst = []
                        for extension in sem:
                            if a in extension:
                                lst.append(True)
                            else:
                                lst.append(False)
                        if any(lst):
                            accepted.add(a)
                return accepted

            def rejected(self, sem):
                rejected = set()
                if len(sem) > 0:
                    for a in self.af.arguments:
                        lst = []
                        for extension in sem:
                            if a in extension:
                                lst.append(False)
                            else:
                                lst.append(True)
                        if all(lst):
                            rejected.add(a)
                return rejected

