CachedSLPToNiceGenerators
Completely independent implementation. Computes an SLP and maybe also the
nicegens, then stores it. Then, whenever someone needs another
SLPToNiceGenerators, this can be taken and evaluated.
Wherever this is called, assert that this and `CalcNiceGens` return the same
group elements, maybe even SLPs with equal `LinesOfSLP`.
