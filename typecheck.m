:- module typecheck.

% An implementation of the algorithm described in
% ``Basic Polymorphic Typechecking'', by Luca Cardelli
% http://lucacardelli.name/Papers/BasicTypechecking.pdf

% Peter Wang <novalazy@gmail.com>

:- interface.

:- import_module assoc_list.
:- import_module io.
:- import_module list.
:- import_module maybe.
:- import_module store.

:- type ide
    --->    ide(string).

:- type exp
    --->    ide(ide)
    ;       cond(exp, exp, exp)
    ;       fun(ide, exp)
    ;       app(exp, exp)
    ;       let(decl, exp).

:- type decl
    --->    def(ide, exp)
    ;       seq(decl, decl)
    ;       rec(decl).

:- type type_exp
    --->    var_type(type_var)
    ;       oper_type(ide, list(type_exp)).

:- type type_var == io_mutvar(maybe(type_exp)).

:- func bool_type = type_exp.

:- func fun_type(type_exp, type_exp) = type_exp.

:- pred new_type_var(type_exp, io, io).
:- mode new_type_var(out, di, uo) is det.

:- pred get_type_var(type_var, maybe(type_exp), io, io).
:- mode get_type_var(in, out, di, uo) is det.

:- type env == assoc_list(ide, type_exp).

:- type ngvars. % non-generic vars

:- func init_ngvars = ngvars.

:- pred analyse_exp(exp, env, ngvars, type_exp, io, io).
:- mode analyse_exp(in, in, in, out, di, uo) is det.

:- type type_error
    --->    unbound_identifier(ide)
    ;       type_clash(type_exp, type_exp)
    ;       different_arities(type_exp, type_exp).

%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- implementation.

:- import_module bool.
:- import_module exception.
:- import_module pair.

%---------------------------------------------------------------------------%

bool_type = oper_type(ide("bool"), []).

fun_type(Domain, Codomain) = oper_type(ide("->"), [Domain, Codomain]).

%---------------------------------------------------------------------------%

new_type_var(var_type(Var), !IO) :-
    new_mutvar(no, Var, !IO).

:- pred same_type(type_exp, type_exp).
:- mode same_type(in, in) is semidet.

same_type(TypeExpA, TypeExpB) :-
    % Relies on pointer equality for type variables.
    TypeExpA = TypeExpB.

get_type_var(Var, MaybeInstantiated, !IO) :-
    get_mutvar(Var, MaybeInstantiated, !IO).

:- pred instantiate_type_var(type_var, type_exp, io, io).
:- mode instantiate_type_var(in, in, di, uo) is det.

instantiate_type_var(Var, TypeExp, !IO) :-
    % The variable must be uninstantiated.
    set_mutvar(Var, yes(TypeExp), !IO).

:- pred prune(type_exp, type_exp, io, io).
:- mode prune(in, out, di, uo) is det.

prune(TypeExp, Pruned, !IO) :-
    (
        TypeExp = var_type(Var),
        get_type_var(Var, MaybeInstantiated, !IO),
        (
            MaybeInstantiated = no,
            Pruned = TypeExp
        ;
            MaybeInstantiated = yes(Instantiated),
            prune(Instantiated, Pruned, !IO),
            instantiate_type_var(Var, Pruned, !IO)
        )
    ;
        TypeExp = oper_type(_, _),
        Pruned = TypeExp
    ).

:- pred occurs_in_type(type_exp, type_exp, bool, io, io).
:- mode occurs_in_type(in, in, out, di, uo) is det.

occurs_in_type(TVar, TypeExp0, Occurs, !IO) :-
    prune(TypeExp0, TypeExp, !IO),
    (
        TypeExp = var_type(_),
        Occurs = pred_to_bool(same_type(TVar, TypeExp))
    ;
        TypeExp = oper_type(_Op, Args),
        occurs_in_type_list(TVar, Args, Occurs, !IO)
    ).

:- pred occurs_in_type_list(type_exp, list(type_exp), bool, io, io).
:- mode occurs_in_type_list(in, in, out, di, uo) is det.

occurs_in_type_list(TVar, List, Occurs, !IO) :-
    (
        List = [],
        Occurs = no
    ;
        List = [Head | Tail],
        occurs_in_type(TVar, Head, Occurs0, !IO),
        (
            Occurs0 = yes,
            Occurs = yes
        ;
            Occurs0 = no,
            occurs_in_type_list(TVar, Tail, Occurs, !IO)
        )
    ).

:- pred unify_type(type_exp, type_exp, io, io).
:- mode unify_type(in, in, di, uo) is det.

unify_type(TypeExpA0, TypeExpB0, !IO) :-
    prune(TypeExpA0, TypeExpA, !IO),
    prune(TypeExpB0, TypeExpB, !IO),
    (
        TypeExpA = var_type(VarA),
        occurs_in_type(TypeExpA, TypeExpB, Occurs, !IO),
        (
            Occurs = yes,
            ( if same_type(TypeExpA, TypeExpB) then
                true
            else
                throw(type_clash(TypeExpA, TypeExpB))
            )
        ;
            Occurs = no,
            instantiate_type_var(VarA, TypeExpB, !IO)
        )
    ;
        TypeExpA = oper_type(TypeOpA, TypeArgsA),
        (
            TypeExpB = var_type(_),
            unify_type(TypeExpB, TypeExpA, !IO)
        ;
            TypeExpB = oper_type(TypeOpB, TypeArgsB),
            ( if TypeOpA = TypeOpB then
                ( if
                    length(TypeArgsA, Arity),
                    length(TypeArgsB, Arity)
                then
                    unify_args(TypeArgsA, TypeArgsB, !IO)
                else
                    throw(different_arities(TypeExpA, TypeExpB))
                )
            else
                throw(type_clash(TypeExpA, TypeExpB))
            )
        )
    ).

:- pred unify_args(list(type_exp), list(type_exp), io, io).
:- mode unify_args(in, in, di, uo) is det.

unify_args(ListA, ListB, !IO) :-
    foldl_corresponding(unify_type, ListA, ListB, !IO).

%---------------------------------------------------------------------------%

:- type ngvars
    --->    ngvars(list(type_exp)).

init_ngvars = ngvars([]).

:- pred is_generic(type_exp, ngvars).
:- mode is_generic(in, in) is semidet.

is_generic(TVar, ngvars(NGVars)) :-
    not contains(NGVars, TVar).

:- pred extend_ngvars(type_exp, ngvars, ngvars).
:- mode extend_ngvars(in, in, out) is det.

extend_ngvars(Var, ngvars(NGVars0), ngvars(NGVars)) :-
    NGVars = [Var | NGVars0].

%---------------------------------------------------------------------------%

:- type copy_env == list(pair(type_exp, type_exp)).

:- pred extend_copy_env(type_exp, type_exp, copy_env, copy_env).
:- mode extend_copy_env(in, in, in, out) is det.

extend_copy_env(Old, New, Tail, CopyEnv) :-
    CopyEnv = [Old - New | Tail].

:- pred fresh_var(type_exp, copy_env, type_exp, copy_env, copy_env, io, io).
:- mode fresh_var(in, in, out, in, out, di, uo) is det.

fresh_var(TypeVar, Scan, TypeExp, !Env, !IO) :-
    (
        Scan = [],
        new_type_var(NewTypeVar, !IO),
        extend_copy_env(TypeVar, NewTypeVar, !Env),
        TypeExp = NewTypeVar
    ;
        Scan = [Old - New | Tail],
        ( if same_type(TypeVar, Old) then
            TypeExp = New
        else
            fresh_var(TypeVar, Tail, TypeExp, !Env, !IO)
        )
    ).

:- pred fresh(ngvars, type_exp, type_exp, copy_env, copy_env, io, io).
:- mode fresh(in, in, out, in, out, di, uo) is det.

fresh(NGVars, TypeExp0, FreshTypeExp, !Env, !IO) :-
    prune(TypeExp0, TypeExp, !IO),
    (
        TypeExp = var_type(_),
        ( if is_generic(TypeExp, NGVars) then
            fresh_var(TypeExp, !.Env, FreshTypeExp, !Env, !IO)
        else
            FreshTypeExp = TypeExp
        )
    ;
        TypeExp = oper_type(Ide, Args),
        map_foldl2(fresh(NGVars), Args, FreshArgs, !Env, !IO),
        FreshTypeExp = oper_type(Ide, FreshArgs)
    ).

:- pred fresh_type(ngvars, type_exp, type_exp, io, io).
:- mode fresh_type(in, in, out, di, uo) is det.

fresh_type(NGVars, TypeExp, FreshTypeExp, !IO) :-
    fresh(NGVars, TypeExp, FreshTypeExp, [], _Env, !IO).

%---------------------------------------------------------------------------%

:- pred extend_env(ide, type_exp, env, env).
:- mode extend_env(in, in, in, out) is det.

extend_env(Ide, TypeExp, !Env) :-
    cons(Ide - TypeExp, !Env).

:- pred retrieve(ide, env, ngvars, type_exp, io, io).
:- mode retrieve(in, in, in, out, di, uo) is det.

retrieve(Ide, Env, NGVars, TypeExp, !IO) :-
    (
        Env = [],
        throw(unbound_identifier(Ide))
    ;
        Env = [HeadIde - HeadTypeExp | EnvTail],
        ( if Ide = HeadIde then
            fresh_type(NGVars, HeadTypeExp, TypeExp, !IO)
        else
            retrieve(Ide, EnvTail, NGVars, TypeExp, !IO)
        )
    ).

%---------------------------------------------------------------------------%

analyse_exp(Exp, Env, NGVars, TypeExp, !IO) :-
    (
        Exp = ide(Ide),
        retrieve(Ide, Env, NGVars, TypeExp, !IO)
    ;
        Exp = cond(Test, Then, Else),
        analyse_exp(Test, Env, NGVars, TestType, !IO),
        unify_type(TestType, bool_type, !IO),
        analyse_exp(Then, Env, NGVars, ThenType, !IO),
        analyse_exp(Else, Env, NGVars, ElseType, !IO),
        unify_type(ThenType, ElseType, !IO),
        TypeExp = ThenType
    ;
        Exp = fun(Binder, Body),
        new_type_var(TypeOfBinder, !IO),
        extend_env(Binder, TypeOfBinder, Env, BodyEnv),
        extend_ngvars(TypeOfBinder, NGVars, BodyNGVars),
        analyse_exp(Body, BodyEnv, BodyNGVars, TypeOfBody, !IO),
        TypeExp = fun_type(TypeOfBinder, TypeOfBody)
    ;
        Exp = app(Fun, Arg),
        analyse_exp(Fun, Env, NGVars, TypeOfFun, !IO),
        analyse_exp(Arg, Env, NGVars, TypeOfArg, !IO),
        new_type_var(TypeOfRes, !IO),
        unify_type(TypeOfFun, fun_type(TypeOfArg, TypeOfRes), !IO),
        TypeExp = TypeOfRes
    ;
        Exp = let(Decl, Scope),
        analyse_decl(Decl, Env, NGVars, DeclEnv, !IO),
        analyse_exp(Scope, DeclEnv, NGVars, TypeExp, !IO)
    ).

:- pred analyse_decl(decl, env, ngvars, env, io, io).
:- mode analyse_decl(in, in, in, out, di, uo) is det.

analyse_decl(Decl, Env, NGVars, DeclEnv, !IO) :-
    (
        Decl = def(Binder, Def),
        analyse_exp(Def, Env, NGVars, TypeOfDef, !IO),
        extend_env(Binder, TypeOfDef, Env, DeclEnv)
    ;
        Decl = seq(First, Second),
        analyse_decl(First, Env, NGVars, DeclEnv1, !IO),
        analyse_decl(Second, DeclEnv1, NGVars, DeclEnv, !IO)
    ;
        Decl = rec(Rec),
        analyse_rec_decl_bind(Rec, Env, RecEnv, NGVars, RecNGVars, !IO),
        analyse_rec_decl(Rec, RecEnv, RecNGVars, !IO),
        DeclEnv = RecEnv
    ).

:- pred analyse_rec_decl_bind(decl, env, env, ngvars, ngvars, io, io).
:- mode analyse_rec_decl_bind(in, in, out, in, out, di, uo) is det.

analyse_rec_decl_bind(Decl, !Env, !NGVars, !IO) :-
    (
        Decl = def(Binder, _),
        new_type_var(NewTypeVar, !IO),
        extend_env(Binder, NewTypeVar, !Env),
        extend_ngvars(NewTypeVar, !NGVars)
    ;
        Decl = seq(First, Second),
        analyse_rec_decl_bind(First, !Env, !NGVars, !IO),
        analyse_rec_decl_bind(Second, !Env, !NGVars, !IO)
    ;
        Decl = rec(Rec),
        analyse_rec_decl_bind(Rec, !Env, !NGVars, !IO)
    ).

:- pred analyse_rec_decl(decl, env, ngvars, io, io).
:- mode analyse_rec_decl(in, in, in, di, uo) is det.

analyse_rec_decl(Decl, Env, NGVars, !IO) :-
    (
        Decl = def(Binder, Exp),
        retrieve(Binder, Env, NGVars, TypeOfBinder, !IO),
        analyse_exp(Exp, Env, NGVars, TypeOfExp, !IO),
        unify_type(TypeOfBinder, TypeOfExp, !IO)
    ;
        Decl = seq(First, Second),
        analyse_rec_decl(First, Env, NGVars, !IO),
        analyse_rec_decl(Second, Env, NGVars, !IO)
    ;
        Decl = rec(Rec),
        analyse_rec_decl(Rec, Env, NGVars, !IO)
    ).

%---------------------------------------------------------------------------%
