:- module test.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- implementation.

:- import_module list.
:- import_module maybe.
:- import_module pair.
:- import_module store.
:- import_module string.

:- import_module typecheck.

%---------------------------------------------------------------------------%

:- func int_type = type_exp.

int_type = oper_type(ide("int"), []).

:- func list_type(type_exp) = type_exp.

list_type(ElemType) = oper_type(ide("list"), [ElemType]).

:- func pair_type(type_exp, type_exp) = type_exp.

pair_type(TypeA, TypeB) = oper_type(ide("pair"), [TypeA, TypeB]).

:- pred test_env(env, io, io).
:- mode test_env(out, di, uo) is det.

test_env(Env, !IO) :-
    new_type_var(A, !IO),
    new_type_var(B, !IO),
    new_type_var(C, !IO),
    new_type_var(D, !IO),
    new_type_var(E, !IO),
    Env = [
        ide("true") - bool_type,
        ide("false") - bool_type,
        ide("0") - int_type,
        ide("3") - int_type,
        ide("succ") - fun_type(int_type, int_type),
        ide("nil") - list_type(A),
        ide("null") - fun_type(B, bool_type),
        ide("tl") - fun_type(list_type(C), list_type(C)),
        ide("pair") - fun_type(D, fun_type(E, pair_type(D, E)))
    ].

main(!IO) :-
    test_env(Env, !IO),
    read(ReadRes, !IO),
    (
        ReadRes = ok(Exp),
        analyse_exp(Exp, Env, init_ngvars, TypeExp, !IO),
        print_type(TypeExp, !IO),
        nl(!IO)
    ;
        ReadRes = eof
    ;
        ReadRes = error(Error, Line),
        format("error on line %d: %s\n", [i(Line), s(Error)], !IO)
    ).

:- pred print_type(type_exp, io, io).
:- mode print_type(in, di, uo) is det.

print_type(TypeExp, !IO) :-
    (
        TypeExp = var_type(Var),
        get_type_var(Var, MaybeInstantiated, !IO),
        (
            MaybeInstantiated = no,
            write_string("_", !IO)
        ;
            MaybeInstantiated = yes(TypeExp1),
            print_type(TypeExp1, !IO)
        )
    ;
        TypeExp = oper_type(ide(Name), Args),
        ( if
            Name = "->",
            Args = [Domain, Codomain]
        then
            print_type(Domain, !IO),
            write_string(" -> ", !IO),
            print_type(Codomain, !IO)
        else
            write_string(Name, !IO),
            (
                Args = []
            ;
                Args = [_ | _],
                write_string("(", !IO),
                write_list(Args, ", ", print_type, !IO),
                write_string(")", !IO)
            )
        )
    ).

%---------------------------------------------------------------------------%
