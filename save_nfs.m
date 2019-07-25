forward write_element;

procedure write_list(ls, file, cfs, save_cm : indent := 0, indent_start := true)
    if indent_start and indent gt 0 then
	Write(file, " " ^ (4 * indent));
    end if;
    Write(file, "[");
    write_comma := false;
    for element in ls do
	if write_comma then Write(file, ","); end if;
	Write(file, "\n");
	write_element(element, file, cfs, save_cm : indent := indent + 1);
	write_comma := true;
    end for;
    Write(file, "]");
end procedure;

procedure write_rational(q, file : indent := 0, indent_start := true)
    if indent_start and indent gt 0 then
	Write(file, " " ^ (4 * indent));
    end if;
    q := Rationals() ! q;
    Write(file, Sprint(q));
end procedure;

procedure write_labeled_element(tup, file, cfs, save_cm : indent := 0)
    label := tup[1];
    element := tup[2];
    if indent gt 0 then
	Write(file, " " ^ (4 * indent));
    end if;
    Write(file, Sprintf("<%o> := ", label));
    if ISA(Type(element), RngElt) and element in Rationals() then
	write_rational(element, file : indent := indent, indent_start := false);
    elif ISA(Type(element), List) or
	 ISA(Type(element), SeqEnum) then
	write_list(element, file, cfs, save_cm : indent := indent, indent_start := false);
    else
       printf "%o, %o is an invalid labeled element", label, element;
    end if;
end procedure;

procedure write_newform(nf, file, cfs, save_cm : indent := 0)
    level := <"level", Level(nf)>;
    if save_cm then
	cm := <"cm", HasCM(ModularSymbols(nf))>;
    else
	cm := <"cm", -1>;
    end if;
    character := DirichletCharacter(nf);
    field := BaseField(nf);
    if not IsAbsoluteField(field) then
	field := AbsoluteField(field);
    end if;
    values := [* *];
    for n in cfs do
	cf := Coefficient(nf, n);
	if cf in Rationals() then
	    cf := Rationals() ! cf;
	else
	    cf := <"element", Eltseq(field ! cf)>;
	end if;
	values := Append(values, [* n, cf *]);
    end for;
    values := <"values", values>;
    element := <"newform", [* level, cm, character, field, values *]>;
    write_labeled_element(element, file, cfs, save_cm : indent := indent);
end procedure;

procedure write_character(eps, file, cfs, save_cm : indent := 0)
    eps := AssociatedPrimitiveCharacter(eps);
    conductor := Conductor(eps);
    K := BaseRing(eps);
    T, m := TorsionUnitGroup(K);
    values := [* [*
		  (Integers() ! n),
		  [ i : i in [0..(Order(T.1)-1)] | m(T.1)^i eq eps(n) ][1]
		  *]
	       : n in Integers(conductor)
	       | Gcd(n, conductor) eq 1 *];
    conductor := <"conductor", conductor>;
    values := <"values", values>;
    element := <"character", [* conductor, values *]>;
    write_labeled_element(element, file, cfs, save_cm : indent := indent);
end procedure;

procedure write_field(K, file, cfs, save_cm : indent := 0)
    if K eq Rationals() then
	R<x> := PolynomialRing(Rationals());
	polynomial := x;
    else
	polynomial := DefiningPolynomial(K);
    end if;
    element := <"field", [* polynomial *]>;
    write_labeled_element(element, file, cfs, save_cm : indent := indent);
end procedure;

procedure write_polynomial(poly, file, cfs, save_cm : indent := 0)
    element := <"polynomial", Coefficients(poly)>;
    write_labeled_element(element, file, cfs, save_cm : indent := indent);
end procedure;

procedure write_element(element, file, cfs, save_cm : indent := 0)
    if ISA(Type(element), List) or
       ISA(Type(element), SeqEnum) then
	write_list(element, file, cfs, save_cm : indent := indent);
    elif ISA(Type(element), ModFrmElt) then
	write_newform(element, file, cfs, save_cm : indent := indent);
    elif ISA(Type(element), Tup) then
	write_labeled_element(element, file, cfs, save_cm : indent := indent);
    elif ISA(Type(element), GrpDrchElt) then
	write_character(element, file, cfs, save_cm : indent := indent);
    elif ISA(Type(element), Fld) then
	write_field(element, file, cfs, save_cm : indent := indent);
    elif ISA(Type(element), RngUPolElt) then
	write_polynomial(element, file, cfs, save_cm : indent := indent);
    elif ISA(Type(element), RngElt) and element in Rationals() then
	write_rational(element, file : indent := indent);
    else
	print "Unrecognized type:", Type(element);
    end if;
end procedure;

procedure save_nfs(nfs, file_name: cfs := 50, repr_cfs := true, save_cm := true)
    if ISA(Type(cfs), RngElt) and cfs in Integers() then
	cfs := { 0..(cfs - 1) };
    end if;
    if repr_cfs then
	cfs := cfs join { 0..19 };
    end if;
    file := Open(file_name, "w+");
    write_element(nfs, file, cfs, save_cm);
    delete file;
end procedure;
