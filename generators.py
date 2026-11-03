class Parent:
    def __init__(self, gender=None):
        self.gender = gender
        self.tag = "P" + (gender if gender is not None else "")


class Child:
    def __init__(self, gender=None):
        self.gender = gender
        self.tag = "C" + (gender if gender is not None else "")


class Mate:
    def __init__(self, gender=None):
        self.gender = gender
        self.tag = "M" + (gender if gender is not None else "")


class Elder:
    def __init__(self, gender=None):
        self.gender = gender
        self.tag = "E" + (gender if gender is not None else "")


class Younger:
    def __init__(self, gender=None):
        self.gender = gender
        self.tag = "Y" + (gender if gender is not None else "")


class Identity:
    def __init__(self, gender=None):
        self.gender = gender
        self.tag = "I" + (gender if gender is not None else "")


class Zero:
    def __init__(self):
        self.tag = "0"
        self.gender = None

