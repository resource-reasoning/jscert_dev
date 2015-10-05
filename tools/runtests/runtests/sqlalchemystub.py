"""
Stub sqlalchemy ORM definition.

Will probably attempt to maintain table relationships in memory
"""


# Helpers
def _empty_function(*args, **argvs):
    return None

# Constants
Boolean = None
Integer = None
DateTime = None
Interval = None
SmallInteger = None
String = None
Text = None

Base = object

# Constructors
Column = _empty_function
Enum = _empty_function


# Might want a real implementation for the rest?
def backref(*args, **argvs):
    return None


def ForeignKey(*args, **argvs):
    return None


def relationship(*args, **argvs):
    return None
