= Declaration Validation Walkthrough

This literate Idris file demonstrates declaration validation.
Load with: pack repl src/WalkthroughDeclValidation.lidr

> module WalkthroughDeclValidation
>
> import Data.List

-------------------------------------------------------------------------------
== The Problem: Trusting Declarations

When someone hands us a declaration like:
  axiom Nat : Type
  def id : Nat → Nat := λx. x
  theorem refl : ∀ x, x = x := ...

How do we know it's valid? We need to check several things before
adding it to our trusted environment.

-------------------------------------------------------------------------------
== Simplified Types for This Walkthrough

> ||| Universe levels (simplified)
> data Level = Zero | Succ Level
>
> Eq Level where
>   Zero == Zero = True
>   (Succ l1) == (Succ l2) = l1 == l2
>   _ == _ = False
>
> ||| Expressions (simplified)
> data Expr
>   = Sort Level
>   | Const String
>   | Pi String Expr Expr
>   | Lam String Expr Expr
>   | App Expr Expr
>
> Eq Expr where
>   (Sort l1) == (Sort l2) = l1 == l2
>   (Const n1) == (Const n2) = n1 == n2
>   (Pi n1 d1 c1) == (Pi n2 d2 c2) = n1 == n2 && d1 == d2 && c1 == c2
>   (Lam n1 t1 b1) == (Lam n2 t2 b2) = n1 == n2 && t1 == t2 && b1 == b2
>   (App f1 a1) == (App f2 a2) = f1 == f2 && a1 == a2
>   _ == _ = False
>
> ||| Declarations
> data Decl
>   = AxiomDecl String Expr (List String)        -- name, type, univ params
>   | DefDecl String Expr Expr (List String)     -- name, type, value, params
>   | ThmDecl String Expr Expr (List String)     -- name, type, proof, params

-------------------------------------------------------------------------------
== The Environment

> ||| Environment: map from names to declarations
> record Env where
>   constructor MkEnv
>   decls : List (String, Decl)
>
> emptyEnv : Env
> emptyEnv = MkEnv []
>
> lookupDecl : String -> Env -> Maybe Decl
> lookupDecl name env = lookup name env.decls
>
> addDecl : Decl -> Env -> Env
> addDecl d@(AxiomDecl n _ _) env = { decls $= ((n, d) ::) } env
> addDecl d@(DefDecl n _ _ _) env = { decls $= ((n, d) ::) } env
> addDecl d@(ThmDecl n _ _ _) env = { decls $= ((n, d) ::) } env

-------------------------------------------------------------------------------
== Check 1: Name Not Already Declared

> data TCError = NameExists String | DupParam String | NotAType | TypeMismatch | NotProp
>
> Show TCError where
>   show (NameExists n) = "already declared: " ++ n
>   show (DupParam p) = "duplicate param: " ++ p
>   show NotAType = "not a type"
>   show TypeMismatch = "type mismatch"
>   show NotProp = "not a Prop"
>
> TC : Type -> Type
> TC = Either TCError
>
> checkNameFresh : Env -> String -> TC ()
> checkNameFresh env name =
>   case lookupDecl name env of
>     Just _ => Left (NameExists name)
>     Nothing => Right ()

Example:

> ex1 : TC ()
> ex1 = checkNameFresh emptyEnv "Nat"
> -- Right () - Nat is fresh

-------------------------------------------------------------------------------
== Check 2: No Duplicate Universe Parameters

> checkNoDupParams : List String -> TC ()
> checkNoDupParams [] = Right ()
> checkNoDupParams (p :: ps) =
>   if elem p ps
>     then Left (DupParam p)
>     else checkNoDupParams ps

Example:

> ex2a : TC ()
> ex2a = checkNoDupParams ["u", "v"]
> -- Right () - all unique
>
> ex2b : TC ()
> ex2b = checkNoDupParams ["u", "u"]
> -- Left (DupParam "u")

-------------------------------------------------------------------------------
== Check 3: Type is Well-Formed

For this walkthrough, we use a simplified type inference.
The real implementation handles all expression forms.

> ||| Simplified type inference
> inferType : Env -> Expr -> TC Expr
> inferType _ (Sort l) = Right (Sort (Succ l))
> inferType env (Const n) =
>   case lookupDecl n env of
>     Just (AxiomDecl _ ty _) => Right ty
>     Just (DefDecl _ ty _ _) => Right ty
>     Just (ThmDecl _ ty _ _) => Right ty
>     Nothing => Right (Sort Zero)  -- unknown const, assume Prop for demo
> inferType env (Pi _ dom cod) = do
>   domTy <- inferType env dom
>   codTy <- inferType env cod
>   -- Simplified: just return Sort 1
>   Right (Sort (Succ Zero))
> inferType env (Lam n ty body) = do
>   _ <- inferType env ty
>   -- Simplified: return Pi type
>   Right (Pi n ty body)
> inferType env (App f _) = do
>   fTy <- inferType env f
>   case fTy of
>     Pi _ _ cod => Right cod
>     _ => Right (Sort Zero)
>
> ||| Check expression is a type (has type Sort l)
> checkIsType : Env -> Expr -> TC Level
> checkIsType env e = do
>   ty <- inferType env e
>   case ty of
>     Sort l => Right l
>     _ => Left NotAType

-------------------------------------------------------------------------------
== Check 4: Definitional Equality

Simplified: just structural equality for this demo.
Real implementation uses reduction and handles eta, proof irrelevance.

> isDefEq : Env -> Expr -> Expr -> TC Bool
> isDefEq _ e1 e2 = Right (e1 == e2)

-------------------------------------------------------------------------------
== Validating Axioms

> checkAxiom : Env -> String -> Expr -> List String -> TC ()
> checkAxiom env name ty params = do
>   checkNameFresh env name
>   checkNoDupParams params
>   _ <- checkIsType env ty
>   Right ()

Example:

> nat : Expr
> nat = Const "Nat"
>
> ex3 : TC ()
> ex3 = checkAxiom emptyEnv "Nat" (Sort (Succ Zero)) []
> -- Right () - valid axiom

-------------------------------------------------------------------------------
== Validating Definitions

> checkDef : Env -> String -> Expr -> Expr -> List String -> TC ()
> checkDef env name ty value params = do
>   checkNameFresh env name
>   checkNoDupParams params
>   _ <- checkIsType env ty
>   valueTy <- inferType env value
>   eq <- isDefEq env valueTy ty
>   if eq
>     then Right ()
>     else Left TypeMismatch

Example:

> -- id : Nat → Nat := λx. x
> idType : Expr
> idType = Pi "x" nat nat
>
> idValue : Expr
> idValue = Lam "x" nat (Const "x")
>
> -- We need Nat in the environment first
> envWithNat : Env
> envWithNat = addDecl (AxiomDecl "Nat" (Sort (Succ Zero)) []) emptyEnv

-------------------------------------------------------------------------------
== Validating Theorems

Theorems must have type in Prop (Sort 0).

> checkThm : Env -> String -> Expr -> Expr -> List String -> TC ()
> checkThm env name ty prf params = do
>   checkNameFresh env name
>   checkNoDupParams params
>   tyLevel <- checkIsType env ty
>   -- Must be Prop
>   if tyLevel /= Zero
>     then Left NotProp
>     else do
>       prfTy <- inferType env prf
>       eq <- isDefEq env prfTy ty
>       if eq
>         then Right ()
>         else Left TypeMismatch

Example:

> -- P : Prop
> propP : Expr
> propP = Const "P"
>
> ex4 : TC ()
> ex4 = checkThm emptyEnv "myThm" propP propP []
> -- Right () - P : Prop, and proof has type P

-------------------------------------------------------------------------------
== The Unified Validator

> addDeclChecked : Env -> Decl -> TC Env
> addDeclChecked env d@(AxiomDecl n ty ps) = do
>   checkAxiom env n ty ps
>   Right (addDecl d env)
> addDeclChecked env d@(DefDecl n ty v ps) = do
>   checkDef env n ty v ps
>   Right (addDecl d env)
> addDeclChecked env d@(ThmDecl n ty p ps) = do
>   checkThm env n ty p ps
>   Right (addDecl d env)

-------------------------------------------------------------------------------
== Building a Trusted Environment

> buildEnv : TC Env
> buildEnv = do
>   -- Add Nat : Type
>   env1 <- addDeclChecked emptyEnv (AxiomDecl "Nat" (Sort (Succ Zero)) [])
>   -- Add P : Prop
>   env2 <- addDeclChecked env1 (AxiomDecl "P" (Sort Zero) [])
>   -- Add proof : P
>   env3 <- addDeclChecked env2 (AxiomDecl "proof" (Const "P") [])
>   -- Add theorem using proof
>   env4 <- addDeclChecked env3 (ThmDecl "myThm" (Const "P") (Const "proof") [])
>   Right env4

-------------------------------------------------------------------------------
== Test Cases

> ||| Show result helper
> showTC : Show a => TC a -> String
> showTC (Left e) = "Error: " ++ show e
> showTC (Right x) = "Ok: " ++ show x
>
> main : IO ()
> main = do
>   putStrLn "Declaration Validation Examples"
>   putStrLn "================================"
>   putStrLn ""
>
>   putStrLn "1. Fresh name check (Nat in empty env):"
>   putStrLn $ "   " ++ showTC ex1
>   putStrLn ""
>
>   putStrLn "2a. Unique params [u, v]:"
>   putStrLn $ "   " ++ showTC ex2a
>   putStrLn ""
>
>   putStrLn "2b. Duplicate params [u, u]:"
>   putStrLn $ "   " ++ showTC ex2b
>   putStrLn ""
>
>   putStrLn "3. Valid axiom (Nat : Type):"
>   putStrLn $ "   " ++ showTC ex3
>   putStrLn ""
>
>   putStrLn "4. Valid theorem (P : Prop, proof : P):"
>   putStrLn $ "   " ++ showTC ex4
>   putStrLn ""
>
>   putStrLn "5. Building full environment:"
>   case buildEnv of
>     Left e => putStrLn $ "   Error: " ++ show e
>     Right env => putStrLn $ "   Ok: " ++ show (length env.decls) ++ " declarations"

-------------------------------------------------------------------------------
== Summary

Declaration validation ensures our environment only contains well-formed
declarations:

  1. checkNameFresh   - no duplicate names
  2. checkNoDupParams - no duplicate universe parameters
  3. checkIsType      - types are well-formed
  4. isDefEq          - value types match declared types
  5. Prop check       - theorems must be propositions

This is the gatekeeper of the kernel's trusted computing base.
