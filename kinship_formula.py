from generators import *
from copy import deepcopy


class KinPolynomial:
    def __init__(self, kin_monomial_list: list):
        self.kin_monomial_list = kin_monomial_list
        self.expression = ' + '.join(km.expression for km in self.kin_monomial_list)
        self.is_zero = all(km.is_zero for km in self.kin_monomial_list)

    def __contains__(self, item):
        if isinstance(item, KinMonomial):
            return item.expression in [km.expression for km in self.kin_monomial_list]
        elif isinstance(item, KinPolynomial):
            return all(km in self for km in item.kin_monomial_list)

    def __eq__(self, other):
        return self in other and other in self

    def __add__(self, other):
        if isinstance(other, KinMonomial):
            return other + self
        elif isinstance(other, KinPolynomial):
            newl = deepcopy(self.kin_monomial_list)
            for km in other.kin_monomial_list:
                if km not in self and not km.is_zero:
                    newl.append(km)
            return KinPolynomial(newl)

    def __mul__(self, other):
        if isinstance(other, KinMonomial):
            return kin_sum(km * other for km in self.kin_monomial_list)
        elif isinstance(other, KinPolynomial):
            return kin_sum(km * other for km in self.kin_monomial_list)

    def __pow__(self, power, modulo=None):
        if type(power) is not int:
            raise TypeError(f"Power should be an integer, got {type(power)}.")
        if modulo is not None:
            raise TypeError("Modulo is Unsupported for Kinship Formula.")
        if power == 0:
            return KinMonomial([Identity()])
        elif self.is_zero or power == 1:
            return self
        elif power > 0:
            res = self
            for _ in range(power - 1):
                res *= self
            return res
        elif power < 0:
            raise ValueError("Negative Power Unsupported. Use inverse() instead.")

    def __repr__(self):
        return self.expression

    def inverse(self, start_gender=None):
        return KinPolynomial([km.inverse(start_gender) for km in self.kin_monomial_list])


class KinMonomial:
    def __init__(self, generator_list: list):
        if len(generator_list) == 0:
            self.generator_list = [Identity()]
        else:
            self.generator_list = generator_list
        self.expression = ''.join(g.tag for g in self.generator_list)
        self.is_zero = (self.expression == '0')
        self.gender = self.generator_list[-1].gender

    def __eq__(self, other):
        if isinstance(other, KinMonomial):
            return self.expression == other.expression
        else:
            return False

    def __add__(self, other):
        if isinstance(other, KinMonomial):
            if self.is_zero:
                return other
            elif other.is_zero:
                return self
            elif self != other:
                return KinPolynomial([self, other])
            else:
                return self
        elif isinstance(other, KinPolynomial):
            if not self.is_zero and self not in other:
                return KinPolynomial([self] + other.kin_monomial_list)
            else:
                return other

    def __mul__(self, other):
        if self.is_zero:
            return self
        if isinstance(other, KinMonomial):
            return init(self.generator_list + other.generator_list)
        elif isinstance(other, KinPolynomial):
            return kin_sum(self * km for km in other.kin_monomial_list)

    def __pow__(self, power: int, modulo=None):
        if type(power) is not int:
            raise TypeError(f"Power should be an integer, got {type(power)}.")
        if modulo is not None:
            raise TypeError("Modulo is Unsupported for Kinship Formula.")
        if power == 0:
            return KinMonomial([Identity()])
        elif self.is_zero or power == 1:
            return self
        elif power > 0:
            return init(self.generator_list * power)
        elif power < 0:
            raise ValueError("Negative Power Unsupported. Use inverse() instead.")

    def __repr__(self):
        return self.expression

    def inverse(self, start_gender=None):
        inverse_dict = {Parent: Child, Child: Parent, Mate: Mate,
                        Elder: Younger, Younger: Elder, Identity: Identity, Zero: Zero}

        new_l = []
        reversed_list = self.generator_list[::-1]
        type_list = [inverse_dict[type(g)] for g in reversed_list]
        gender_list = [g.gender for g in reversed_list[1:]] + [start_gender]
        for i in range(len(self.generator_list)):
            new_l.append(type_list[i](gender_list[i]))
        return KinMonomial(new_l)


def init(generator_list: list):
    class _Temp_Term:
        def __init__(self):
            self.content = []

        def last(self):
            if self.content:
                return self.content[-1]
            else:
                return None

        def put_in(self, s):
            self.content.append(s)

        def take_out_last(self):
            return self.content.pop()

    def copyTerm(t: _Temp_Term):
        return deepcopy(t)

    def transform(s1, s2):
        if type(s1) is Zero or type(s2) is Zero:
            return Zero()

        elif type(s2) is Identity:
            if s2.gender != s1.gender and s2.gender is not None:
                return Zero()
            else:
                return s1
        elif type(s1) is Identity:
            return s2

        elif type(s1) is Parent:
            if type(s2) is Child:
                return Elder(s2.gender), Identity(s2.gender), Younger(s2.gender)
            elif type(s2) is Mate:
                return Parent(s2.gender)
        elif type(s1) is Mate:
            if type(s2) is Child:
                return s2
            elif type(s2) is Mate:
                return Identity(s2.gender)
        elif type(s1) is Child:
            if type(s2) is Parent:
                return Mate(s2.gender), Identity(s2.gender)
            elif isinstance(s2, (Elder, Younger)):
                return Child(s2.gender)
        elif isinstance(s1, (Elder, Younger)):
            if type(s2) is Parent:
                return s2
            elif isinstance(s2, (Elder, Younger)):
                if type(s1) is type(s2):
                    return s2
                else:
                    return Elder(s2.gender), Identity(s2.gender), Younger(s2.gender)

    def tryToPutIn(t: _Temp_Term, s):
        if s is None:
            return ()
        last = t.last()
        if last is None:
            t.put_in(s)
            return (t,)
        else:
            if (isinstance(last, (Parent, Mate)) and isinstance(s, (Parent, Elder, Younger))) or (isinstance(last, (Elder, Younger, Child)) and isinstance(s, (Child, Mate))):
                t.put_in(s)
                return (t,)
            else:
                new = transform(t.take_out_last(), s)
                if type(new) is not tuple:
                    return tryToPutIn(t, new)
                else:
                    if len(new) == 2:
                        newt = copyTerm(t)
                        return tryToPutIn(t, new[0]) + tryToPutIn(newt, new[1])
                    elif len(new) == 3:
                        newt, newt2 = copyTerm(t), copyTerm(t)
                        return tryToPutIn(t, new[0]) + tryToPutIn(newt, new[1]) + tryToPutIn(newt2, new[2])

    result = [_Temp_Term()]
    if len(generator_list) == 0:
        return KinMonomial([Identity()])
    else:
        for s in generator_list:
            new_result = ()
            for t in result:
                new_result += tryToPutIn(t, s)
            result = new_result

    l = []
    zero_km = KinMonomial([Zero()])
    for r in result:
        km = KinMonomial(r.content)
        if km != zero_km and km not in l:
            l.append(km)
    if len(l) == 1:
        return l[0]
    elif len(l) >= 2:
        return KinPolynomial(l)
    else:
        return zero_km


def kin_sum(__iterable):
    zero = KinMonomial([Zero()])
    return sum(__iterable, zero)


def kinship_type(formula: KinMonomial):
    ktype = "B"
    for g in formula.generator_list:
        if isinstance(g, (Elder, Younger)):
            ktype = "C"
        elif isinstance(g, Mate):
            ktype = "M"
            break
    return ktype


def priority(formula: KinMonomial):
    p = 0
    for g in formula.generator_list:
        if isinstance(g, Parent):
            p += 1
        elif isinstance(g, Child):
            p -= 1
    return p

