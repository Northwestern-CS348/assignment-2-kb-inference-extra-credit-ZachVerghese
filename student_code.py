import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Implementation goes here
        # Not required for the extra credit assignment

    def kb_explain(self, fact_or_rule):
        """
        Explain where the fact or rule comes from

        Args:
            fact_or_rule (Fact or Rule) - Fact or rule to be explained

        Returns:
            string explaining hierarchical support from other Facts and rules
        """
        ####################################################
        # Student code goes here
        originalfactrule = ""
        supported = ""
        if isinstance(fact_or_rule,Fact):
            thefact = self._get_fact(fact_or_rule)
            if thefact in self.facts:
                originalfactrule = "fact: "+ thefact.statement.__str__()
                if thefact.asserted:
                    originalfactrule += "  ASSERTED"
                originalfactrule += "\n"
                if thefact.supported_by:
                    originalfactrule += self.get_supported(thefact,0)
                print(originalfactrule)
                return originalfactrule
            else:
                return "Fact is not in the KB"
        elif isinstance(fact_or_rule,Rule):
            therule = self._get_rule(fact_or_rule)
            if therule in self.rules:
                originalfactrule = "rule: " + self.create_rule_list(therule)
                if therule.asserted:
                    originalfactrule += " ASSERTED"
                originalfactrule += "\n"
                if therule.supported_by:
                    originalfactrule += self.get_supported(therule,0)
                print(originalfactrule)
                return originalfactrule
            else:
                return "Rule is not in the KB"
        else:
            return "Not a fact or rule"

    def get_supported(self,fact_or_rule, indent):
        indent+=2
        supported = ""
        for thing in fact_or_rule.supported_by:
            supported += (indent * " ") + "SUPPORTED BY\n"
            # fact
            if thing[0].asserted:
                supported += ((indent+2)* " ") + "fact: " + thing[0].statement.__str__() + " ASSERTED\n"
            else:
                supported += ((indent+2)* " ") + "fact: " + thing[0].statement.__str__() + "\n"
            supported += self.get_supported(thing[0], indent+2)
            #rule
            if thing[1].asserted:
                supported += ((indent+2)* " ") + "rule: " + self.create_rule_list(thing[1]) + " ASSERTED\n"
            else:
                supported += ((indent+2)* " ") + "rule: " + self.create_rule_list(thing[1]) + "\n"
            supported += self.get_supported(thing[1],indent+2)
        return supported
    
    def create_rule_list(self,the_rule):
        rule_list = "("
        for i, left_element in enumerate(the_rule.lhs):
            if i != len(the_rule.lhs) -1:
                rule_list += left_element.__str__() + ", "
            else:
                rule_list+= left_element.__str__() + ") -> " + the_rule.rhs.__str__()
        return rule_list
            






class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Implementation goes here
        # Not required for the extra credit assignment
