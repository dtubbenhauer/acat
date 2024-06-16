# Code and Erratum for *On the asymptotic category*

I collected a bit of Magma code relevant for the paper *On the asymptotic category*
<a href="https://arxiv.org/abs/2307.03044">https://arxiv.org/abs/2307.03044</a> on this page.

The code is in a **.odt** file or **.n** file, respectively, that can be downloaded from this site and you can run it with Magma.

An Erratum for the paper *On the asymptotic category* can be found at the bottom of the page.

# Contact

If you find any errors in the paper *On the asymptotic category* **please email me**:

[dtubbenhauer@gmail.com](mailto:dtubbenhauer@gmail.com?subject=[GitHub]%web-reps)

Same goes for any errors related to this page.


# Background

The paper *On the asymptotic category* identifies the asymtotic (Hecke) category $\mathbf{A}_{\mathcal{H}}$ for diagonal H-cells $\mathcal{H}$ and all finite Coxeter types with few exceptions. 
Let us go through the cases, with reference to the list of irreducible finite Coxeter groups as e.g. here: <a href="https://en.wikipedia.org/wiki/Coxeter_group#Classification">https://en.wikipedia.org/wiki/Coxeter_group#Classification</a>.

- First, if the Coxeter type is classical (types A,B,C,D), then $\mathbf{A}_{\mathcal{H}}$ is a well-known and uncomplicated fusion category, namely the category $\mathbf{Vec}(G)$ of vector spaces graded by an elementary abelian 2-group $G$.

- In all other types we list in the paper what we expect the asymtotic category to be, and also when we were able to verify that it is what it is.

The idea is that one can identify $\mathbf{A}_{\mathcal{H}}$ by computing cateogrical dimensions, and the program below can do that using Magma.

# The Magma code

The Magma code can be downloaded on this page. Its called **idempotent_tests.m**. To run it:

- First, setup Joel Gibson's ASLoc which can be found here <a href="https://github.com/joelgibson/asloc">https://github.com/joelgibson/asloc</a>.

- Then you can start the file in your ASLoc folder.

- As soon as its started run one of the procedures listed below. The output will be of the form:

![Output](https://github.com/dtubbenhauer/acat/blob/main/g2.png)

The available procedures are:

```
B2_complete()
G2_complete()
H3_a1_complete()
H3_a3_complete()
H3_long_complete()
H4_complete()
H4_middle_1()
H4_middle_9()
H4_middle_19()
```

**Small warning**: Some of these run for quite some time.

# Erratum

Empty so far.

