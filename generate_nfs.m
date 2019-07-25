load "save_nfs.m";

cf := 500; // Upper bound on the coefficients to be saved
cm := false; // Choose to save whether a newform has CM. Takes long if set to true.
N1 := 11520;
N2 := 23040;
N3 := 15360;
K := CyclotomicField(4);
i := K.1;

D15 := DirichletGroup(15, K);
eps15 := Elements(D15)[1];
for eps in Elements(D15) do
    if eps(11) eq -1 and eps(7) eq i then
	eps15 := eps;
	break;
    end if;
end for;

D1 := DirichletGroup(N1, K);
eps1 := D1 ! eps15;
cfs1 := CuspForms(eps1);
nfs1 := Newforms(cfs1);

D2 := DirichletGroup(N2, K);
eps2 := D2 ! eps15;
cfs2 := CuspForms(eps2);
nfs2 := Newforms(cfs2);

D3 := DirichletGroup(N3, K);
eps3 := D3 ! eps15;
cfs3 := CuspForms(eps3);
nfs3 := Newforms(cfs3);

save_nfs([*nfs1, nfs2*], "tmp/E1.nfs": cfs := cf, save_cm := cm);
save_nfs(nfs3, "tmp/E2.nfs": cfs:= cf, save_cm := cm);
