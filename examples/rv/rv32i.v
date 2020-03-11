(*! Pipelined instantiation of an RV32I core !*)
Require Import RV.RVCore RV.rv32.
Module RV32IPackage := Package RV32I.
Definition prog := Interop.Backends.register RV32IPackage.package.
Extraction "rv32i.ml" prog.
