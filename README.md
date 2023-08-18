# gol-preim

A Python program for finding Game of Life patterns with constrained preimages.

## Description

The file `patfinder.py` implements a backtracking hill-climbing algorithm that finds specific kinds of finite patterns of Game of Life.
The user can specify the following types of constraints for the target pattern **P**:
* For a finite domain **D** and a set **S** of subpatterns of shape **D**, every preimage **Q** of **P** has a pattern of **S** at **D**, and all patterns of **S** occur in preimages in this way.
* If a preimage contains a specific subpattern **Q** at a certain position, then it contains another specific pattern at **D**.
* The pattern **P** does not extend to a certain domain, or contains ony 0s in a certain domain.
* The pattern **P** is peridic in a certain direction.
* Etc.

The search can take a long time, hitting dead ends and backtracking repeatedly, but still eventually succeed.
On the other hand, it may not finish after all, if the constraints are too strict or just unluckily chosen.

## Dependencies

The program depends on the [python-sat](https://pypi.org/project/python-sat/) package.

## Usage

The most important part of the file `patfinder.py` is the `Finder` class.
It accepts the following arguments, only the first of which is mandatory:
* `forced`: a list of pairs `(f, L)`, where `f` is a function that takes a 2D vector and returns 0, 1 or `None`, and `L` is a list of finite patterns with common domain **D**, encoded as dictionaries of 2D vectors to integers. The semantics is that among those perimages of **P** that are compatible with `f`, restricting to **D** should produce exactly the patterns of `L`.
* `chunks` is a list of sets that together cover the domain **D**.
* `allowed` is a function from 2D vectors to Booleans, specifying where the program is allowed to extend **P**.
* `pat` is an initial seed for **P**.
* `line` is an enumeration of the outer border of `pat`.
* `relv` is a list of lists of lists of patterns. It contains, for each pair `(f,L)` in `forced` and for each set in `chunks`, a list of patterns that have not yet been forbidden from occurring in preimages.
* `allow_diamonds` lets the user specify if they want to forbid "diamonds", i.e. pairs of preimages of **P** that agree near the border of **P**, one of which contains a pattern from a list `L` and the other one does not. Such pairs may indicate that the search is unlikely to be finished succesfully, but may take a long time before backtracking.
* `blen` sets the size of the next attempted extension.
* `use_corners` specifies whether **P** can be extended by a corner-adjacent cell.
* `merge_bound` controls when two lists of relevant patterns are short enough that the corresponding chunks can be merged.
* `fill_state` is a function that takes a 2D vector and returns 0, 1 or `None`. It can be used to specify the state of forbidden cells of **P**.
* `period` forces **P** and its preimages to be periodic in the given direction.
* `prune_subsets` will prune all superpatterns of already seen patterns from the search tree, in addition to the patterns themselves.
* `existential` specifies that one pattern of `L` occurring in some preimage is enough, as opposed to all of them.

After initialization, a `Finder` object `finder` can be controlled as follows:
* `finder.pat` contains the pattern **P**.
* `finder.extend_until_null()` tries to extend **P** until its score becomes 0, i.e. it satisfies the given constraints. The pattern is extended 1-5 cells at a time to decrease its score, or failing that, with a randomly chosen rectangular chunk. The program backtracks automatically from dead ends. Returns `True` for a successful search or `False` for an unsuccessful one.
* `finder.complete_to_rect()` will complete the finished pattern **P** into a rectangle, favoring 0-cells whenever possible.

The file `example.py` contains a simple usage example.