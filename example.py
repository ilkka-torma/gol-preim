# Example file for using patfinder

from patfinder import *

if __name__ == "__main__":

    # We search for a pattern P with the following properties:
    # 1) The pattern is wholly contained in the upper half plane.
    # 2) Every preimage of the pattern contains one of the subpatterns
    #    111
    #    000
    #    so that the bottom left 0 is at the origin.

    # The two forced patterns
    forced = [({}.get, [from_mat([[1,0,1,0],[1,0,1,0]])])]
              
    # The region where we are allowed to put cells of P
    allowed = lambda vec: vec[1] >= 0

    # Define the Finder object
    finder = Finder(forced, allowed=allowed)

    # Run the search
    finder.extend_until_null()

    # When a pattern is found, print it
    print("Finished!")
    prettyprint(finder.pat)