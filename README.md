# Quatum-Computing-Reasoning
Isabelle HOL semantics and Hoare Logic with Separation for reasoning in Quantum Computing

This work based of our semantics for quantum computing. This mechanization adds some changes for a better fitting of the non-mechanized semantics into the Isabelle/HOL theorem prover. It also adds some small improvements over the original semantics. 

INSTALLATION

The current version works under Isabelle HOL 2020. You can download Isabelle HOL from 
https://isabelle.in.tum.de/

In Linux and macOS, after installing Isabelle/HOL add the "bin" folder to the system path. 

In windows this is not necessary since Isabelle runs under cygwing and the distributions provide a script to load the necessary environment variables. That script must be executed, which will open a cygwin shell.

This project relies on many different theories from the Isabelle HOL Archive of Formal Proofs. It is therefore necessary to first download it from https://www.isa-afp.org/release/afp-current.tar.gz and copy it to some directory. To properly refer the AFP into this project, it is necessary to modify the ROOTS file with the path to the "thys" folder inside afp. For example, if the afp is installed in: /users/myuser/afp/ the ROOTS file must contain the line /users/myuser/afp/thys

Finally, open a shell, navigate to the root of the project, and execute the following command:

isabelle jedit -d . 

and drag and drop any .thy file to inspect it.
