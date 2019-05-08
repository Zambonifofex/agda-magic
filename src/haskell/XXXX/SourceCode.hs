module XXXX.SourceCode
	(
		Module(..),
		TypeDeclaration(..),
		Datatype(..),
		RecordType(..),
		DelegatedType(..),
		Direction(..),
		Fixity(..),
		Name(..),
		Function(..),
		Visibility(..),
		Type(..),
		show_module
	)
	where

import Data.List (intercalate)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prelude hiding (Left, Right)
import Data.Graph (flattenSCC, stronglyConnComp)

data Module =
	Module
	{
		module_name :: String,
		module_types :: [TypeDeclaration],
		module_functions :: [Function],
		module_reexports :: Imports,
		module_postulated_types :: [Function]
	}

data TypeDeclaration =
	Datatype Datatype |
	RecordType RecordType |
	DelegatedType DelegatedType

data Datatype =
	Data
	{
		datatype_name :: Name,
		datatype_type :: Type,
		datatype_parameters :: [(Visibility, String, Type)],
		datatype_constructors :: [Function]
	}

data RecordType =
	Record
	{
		record_type_name :: Name,
		record_type_fields :: [Function],
		record_type_parameters :: [(Visibility, String, Type)]
	}

data DelegatedType =
	Delegate
	{
		delegated_type_name :: Name,
		delegated_type_parameters :: [String],
		delegated_type_delegation :: Type,
		delegated_type_type :: Type
	}

data Direction = Left | Right | None

data Fixity = Infix Direction Integer

data Name =
	Name
	{
		name_string :: String,
		name_fixity :: Maybe Fixity,
		name_is_operator :: Bool
	}

data Function =
	Function
	{
		function_name :: Name,
		function_type :: Type
	}

data Visibility = Explicit | Inferred | Instance
	deriving Eq

data Type =
	Application Type Type |
	ForAll Visibility String Type Type |
	Named String String
	deriving Eq

par :: String -> String
par str = "(" ++ str ++ ")"

show_application_f :: Type -> String
show_application_f f@(Application _ _) = show_type f
show_application_f f@(ForAll _ _ _ _) = par (show_type f)
show_application_f f@(Named _ _) = show_type f

show_application_a :: Type -> String
show_application_a a@(Application _ _) = par (show_type a)
show_application_a a@(ForAll _ _ _ _) = par (show_type a)
show_application_a a@(Named _ _) = show_type a

references :: Type -> String -> Bool
references _ "_" = False
references (Application f a) name = references f name || references a name
references (ForAll _ name2 l r) name = references l name || name /= name2 && references r name
references (Named "" name2) name = name == name2
references (Named _ _) _ = False

group_forall_inferred :: Type -> Type -> ([String], Type)
group_forall_inferred t@(ForAll Inferred name l r) q = if l /= q then ([], t) else (name : fst next, snd next)
	where next = group_forall_inferred r q
group_forall_inferred t _ = ([], t)

group_forall_instance :: Type -> Type -> ([String], Type)
group_forall_instance t@(ForAll Instance name l r) q = if l /= q then ([], t) else (name : fst next, snd next)
	where next = group_forall_instance r q
group_forall_instance t _ = ([], t)

sp :: [String] -> String
sp = intercalate " "

group_forall_explicit :: Bool -> Type -> Type -> ([String], Type)
group_forall_explicit force t@(ForAll Explicit name l r) q = if l == q && (force || references r name) then (name : fst next, snd next) else ([], t)
	where next = group_forall_explicit force r q
group_forall_explicit force t@(ForAll Inferred _ l _) q = if l /= q then ([], t) else (("{" ++ sp (fst group) ++ "}") : fst next, snd next)
	where
	group = group_forall_inferred t q
	next = group_forall_explicit force (snd group) q
group_forall_explicit force t@(ForAll Instance _ l _) q = if l /= q then ([], t) else (("\x2983 " ++ sp (fst group) ++ " \x2984") : fst next, snd next)
	where
	group = group_forall_instance t q
	next = group_forall_explicit force (snd group) q
group_forall_explicit force t _ = ([], t)

show_forall_type :: Type -> String
show_forall_type (Named "" "_") = ""
show_forall_type t = " : " ++ show_type t

show_forall_group :: Type -> String
show_forall_group t@(ForAll Inferred _ l _) = "{" ++ sp (fst group) ++ show_forall_type l ++ "} " ++ show_forall_next (snd group)
	where group = group_forall_inferred t l
show_forall_group t@(ForAll Instance _ l _) = "\x2983 " ++ sp (fst group) ++ show_forall_type l ++ " \x2984 " ++ show_forall_next (snd group)
	where group = group_forall_instance t l
show_forall_group t@(ForAll Explicit _ l@(Named "" "_") _) = sp (fst group) ++ " " ++ show_forall_next (snd group)
	where group = group_forall_explicit False t l
show_forall_group t@(ForAll Explicit _ l _) = if (fst group) == [] then show_type t else "(" ++ sp (fst group) ++ show_forall_type l ++ ") " ++ show_forall_next (snd group)
	where group = group_forall_explicit False t l

group_datatype_forall :: Type -> String
group_datatype_forall t@(ForAll Inferred _ l _) = "{" ++ sp (fst group) ++ show_forall_type l ++ "} " ++ group_datatype_forall (snd group)
	where group = group_forall_inferred t l
group_datatype_forall t@(ForAll Instance _ l _) = "\x2983 " ++ sp (fst group) ++ show_forall_type l ++ " \x2984 " ++ group_datatype_forall (snd group)
	where group = group_forall_instance t l
group_datatype_forall t@(ForAll Explicit _ l@(Named "" "_") _) = sp (fst group) ++ " " ++ group_datatype_forall (snd group)
	where group = group_forall_explicit True t l
group_datatype_forall t@(ForAll Explicit _ l _) = "(" ++ sp (fst group) ++ show_forall_type l ++ ") " ++ group_datatype_forall (snd group)
	where group = group_forall_explicit True t l
group_datatype_forall _ = ""

show_forall_l, show_forall_r :: Type -> String

show_forall_l t@(Application _ _) = show_type t
show_forall_l t@(ForAll _ _ _ _) = par (show_type t)
show_forall_l t@(Named _ _) = show_type t

show_forall_r = show_type

show_forall_next :: Type -> String
show_forall_next t@(ForAll Explicit name _ r) | references r name = show_forall_group t
show_forall_next t@(ForAll visibility _ _ _) | visibility /= Explicit = show_forall_group t
show_forall_next t = "\x2192 " ++ show_forall_r t

show_forall :: Type -> String
show_forall t@(ForAll Explicit name l r) | not (references r name) = show_forall_l l ++ " \x2192 " ++ show_forall_r r
show_forall t = "\x2200 " ++ show_forall_group t

show_type (Named "" name) = name
show_type (Named mod name) = mod ++ "." ++ name
show_type (Application f a) = show_application_f f ++ " " ++ show_application_a a
show_type t@(ForAll _ _ _ _) = show_forall t

unqualify_type :: Imports -> [String] -> String -> Type -> Type
unqualify_type im ns current (Named mod name) = if mod == current || not (elem name ns) && (Set.member name (Map.findWithDefault Set.empty mod im)) then Named "" name else Named mod name
unqualify_type im ns current (Application f a) = Application (unqualify_type im ns current f) (unqualify_type im ns current a)
unqualify_type im ns current (ForAll v name l r) = ForAll v name (unqualify_type im ns current l) (unqualify_type im ns' current r)
	where ns' = name : ns

agda_name :: Name -> String
agda_name n | name_is_operator n = "_" ++ name_string n ++ "_"
agda_name n = name_string n

-- haskell_name :: Name -> String
-- haskell_name n | name_is_operator n = par $ name_string n
-- haskell_name n = name_string n

show_function_signature :: Function -> String
show_function_signature f = agda_name (function_name f) ++ " : " ++ show_type (function_type f)

show_function_signature_with_fixity :: Function -> String
show_function_signature_with_fixity f = join [show_fixity $ function_name f, show_function_signature f]

join, join2 :: [String] -> String
join = intercalate "\n" . filter ("" /=)
join2 = intercalate "\n\n" . filter ("" /=)

indentation = "   "

indent', indent :: String -> String
indent' ('\n' : str) = '\n' : indentation ++ indent' str
indent' (a : str) = a : indent' str
indent' "" = ""

indent str = indentation ++ (indent' str)

forced_block_string, block_string :: String -> String -> String

forced_block_string name lines = name ++ "\n" ++ indent lines

block_string _ "" = ""
block_string names lines = forced_block_string names lines

forced_block, block, short_block :: String -> [String] -> String
forced_block name lines = forced_block_string name (join lines)
block name lines = block_string name (join lines)
short_block name (line : []) = name ++ " " ++ line
short_block name lines = block name lines

show_mod :: Imports -> Module -> String
show_mod im m =
	join2
	[
		"module " ++ mod ++ " where",
		show_imports im,
		"import Agda.Primitive",
		"private variable \x2113 : Agda.Primitive.Level",
		block "postulate" (map show_function_signature_with_fixity $ module_postulated_types m),
		show_type_declarations (module_types m),
		block "postulate" (map show_function_signature_with_fixity $ module_functions m)
	]
	where mod = module_name m

show_module :: Module -> String
show_module mod = show_mod im $ unqualify_module im mod
	where im = normalize_imports $ generate_imports mod

type Imports = Map String (Set String)

merge_imports :: Imports -> Imports -> Imports
merge_imports = Map.unionWith Set.union

imports_from_type :: Type -> Imports
imports_from_type (Named "" _) = Map.empty
imports_from_type (Named mod id) = Map.singleton mod (Set.singleton id)
imports_from_type (Application l r) = merge_imports (imports_from_type l) (imports_from_type r)
imports_from_type (ForAll _ _ f a) = merge_imports (imports_from_type f) (imports_from_type a)

generate_imports :: Module -> Imports
generate_imports mod = Map.filterWithKey (flip $ const $ (module_name mod /=)) $ foldr (merge_imports . imports_from_type . function_type) Map.empty (module_functions mod)

normalize_imports :: Imports -> Imports
normalize_imports = (. Map.toList) $ snd . foldl (\ (insofar, result) (mod_name, ids) -> (Set.union insofar ids, Map.insert mod_name (Set.difference ids insofar) result)) (Set.empty, Map.empty)

show_import :: String -> Set String -> String
show_import mod im | Set.null im = "import " ++ mod
show_import mod im = "open import " ++ mod ++ " using (" ++ intercalate " ; " (Set.toList im) ++ ")"

show_imports :: Imports -> String
show_imports im = join $ map (uncurry show_import) (Map.toList im)

show_direction :: Direction -> String
show_direction Left = "infixl"
show_direction Right = "infixr"
show_direction None = "infix"

show_fixity :: Name -> String
show_fixity Name {name_fixity = Nothing} = ""
show_fixity Name {name_string = name, name_fixity = Just (Infix direction precedence)}
	= show_direction direction ++ " " ++ show precedence ++ " " ++ name

show_record_type :: RecordType -> String
show_record_type declaration = forced_block (show_record_type_signature declaration ++ " where") (record_type_body declaration)

show_record_type_signature :: RecordType -> String
show_record_type_signature declaration =
	join
	[
		show_fixity (record_type_name declaration),
		"record " ++ agda_name (record_type_name declaration) ++ " " ++ group_datatype_forall parameter_types ++ ": Set \x2113"
	]
	where
	placeholder = Named "" "__"
	parameter_types = foldr (\ (v, n, l) r -> ForAll v n l r) placeholder (record_type_parameters declaration)

record_type_body :: RecordType -> [String]
record_type_body declaration =
	[
		join $ map (show_fixity . function_name) (record_type_fields declaration),
		short_block "field" $ map show_function_signature (record_type_fields declaration)
	]

show_record_type_definition :: RecordType -> String
show_record_type_definition declaration =
	forced_block ("record " ++ agda_name (record_type_name declaration) ++ " " ++ concatMap (show_parameter occurences) (record_type_parameters declaration) ++ " where")
		$ record_type_body declaration
	where occurences = map function_type (record_type_fields declaration)

show_datatype :: Datatype -> String
show_datatype declaration =
	join2
	[
		join $ map (show_fixity . function_name) (datatype_constructors declaration),
		forced_block (show_datatype_signature declaration ++ " where")
			$ map show_function_signature (datatype_constructors declaration)
	]

show_datatype_signature :: Datatype -> String
show_datatype_signature declaration =
	join
	[
		show_fixity (datatype_name declaration),
		"data " ++ agda_name (datatype_name declaration) ++ " " ++ group_datatype_forall parameter_types ++ ": " ++ show_type (datatype_type declaration)
	]
	where
	placeholder = foldl Application (Named "" "__") (datatype_type declaration : map function_type (datatype_constructors declaration))
	parameter_types = foldr (\ (v, n, l) r -> ForAll v n l r) placeholder (datatype_parameters declaration)

show_required_parameter :: (Visibility, String, Type) -> String
show_required_parameter (Explicit, name, _) = name ++ " "
show_required_parameter (Inferred, name, _) = "{" ++ name ++ " = " ++ name ++ "} "
show_required_parameter (Instance, name, _) = "\x2983 " ++ name ++ " = " ++ name ++ " \x2984 "

show_unrequired_parameter :: (Visibility, String, Type) -> String
show_unrequired_parameter (Explicit, _, _) = "_ "
show_unrequired_parameter _ = ""

show_parameter :: [Type] -> (Visibility, String, Type) -> String
show_parameter locations parameter@(visibility, name, _) =
	if any (flip references name) locations
	then show_required_parameter parameter
	else show_unrequired_parameter parameter

show_datatype_definition :: Datatype -> String
show_datatype_definition declaration =
	join2
	[
		join $ map (show_fixity . function_name) (datatype_constructors declaration),
		forced_block ("data " ++ agda_name (datatype_name declaration) ++ " " ++ concatMap (show_parameter occurences) (datatype_parameters declaration) ++ "where")
			$ map show_function_signature (datatype_constructors declaration)
	]
	where occurences = map function_type (datatype_constructors declaration)

unqualify_function :: Imports -> [String] -> String -> Function -> Function
unqualify_function im ns current f = f {function_type = unqualify_type im ns current (function_type f)}

unqualify_module :: Imports -> Module -> Module
unqualify_module im mod =
	mod
	{
		module_types = map (unqualify_type_declaration im current) (module_types mod),
		module_functions = map (unqualify_function im [] current) (module_functions mod)
	}
	where current = module_name mod

unqualify_type_declaration :: Imports -> String -> TypeDeclaration -> TypeDeclaration
unqualify_type_declaration im current (Datatype declaration) =
	Datatype declaration
	{
		datatype_type = unqualify_type im ns current (datatype_type declaration),
		datatype_parameters = unqualify_parameters im ns current (datatype_parameters declaration),
		datatype_constructors = map (unqualify_function im ns current) (datatype_constructors declaration)
	}
	where ns = map (\ (_, n, _) -> n) (datatype_parameters declaration)
unqualify_type_declaration im current (RecordType declaration) =
	RecordType declaration
	{
		record_type_parameters = unqualify_parameters im ns current (record_type_parameters declaration),
		record_type_fields = map (unqualify_function im [] current) (record_type_fields declaration)
	}
	where ns = map (\ (_, n, _) -> n) (record_type_parameters declaration)
unqualify_type_declaration im current (DelegatedType declaration) =
	DelegatedType declaration
	{
		delegated_type_type = unqualify_type im [] current (delegated_type_type declaration),
		delegated_type_delegation = unqualify_type im (delegated_type_parameters declaration) current (delegated_type_delegation declaration)
	}

unqualify_parameters :: Imports -> [String] -> String -> [(Visibility, String, Type)] -> [(Visibility, String, Type)]
unqualify_parameters _ _ _ [] = []
unqualify_parameters im ns current ((visibility, name, ty) : params) = (visibility, name, unqualify_type im ns current ty) : unqualify_parameters im (name : ns) current params

organize :: [TypeDeclaration] -> [[TypeDeclaration]]
organize declarations = map flattenSCC $ stronglyConnComp (type_declaration_graph declarations)

type_declaration_vertex :: TypeDeclaration -> (TypeDeclaration, String, [String])
type_declaration_vertex declaration =
	(
		declaration,
		type_declaration_name declaration,
		type_declaration_all_references declaration
	)

type_declaration_graph = map type_declaration_vertex

function_all_references :: Function -> [String]
function_all_references f = type_all_references (function_type f)

type_all_references :: Type -> [String]
type_all_references (Application f a) = type_all_references f ++ type_all_references a
type_all_references (ForAll _ _ l r) = type_all_references l ++ type_all_references r
type_all_references (Named "" name) = [name]
type_all_references (Named _ _) = []

type_declaration_all_references :: TypeDeclaration -> [String]
type_declaration_all_references (Datatype declaration) =
	type_all_references (datatype_type declaration) ++
	concatMap (function_all_references) (datatype_constructors declaration) ++
	concatMap (\ (_, _, ty) -> type_all_references ty) (datatype_parameters declaration)
type_declaration_all_references (RecordType declaration) =
	concatMap (\ (_, _, ty) -> type_all_references ty) (record_type_parameters declaration) ++
	concatMap (function_all_references) (record_type_fields declaration)
type_declaration_all_references (DelegatedType declaration) = type_all_references (delegated_type_delegation declaration)

type_declaration_name :: TypeDeclaration -> String
type_declaration_name (Datatype declaration) = name_string $ datatype_name declaration
type_declaration_name (RecordType declaration) = name_string $ record_type_name declaration
type_declaration_name (DelegatedType declaration) = name_string $ delegated_type_name declaration

show_delegated_type_signature :: DelegatedType -> String
show_delegated_type_signature declaration = show_function_signature_with_fixity (Function {function_name = delegated_type_name declaration, function_type = delegated_type_type declaration})

show_delegated_type_definition :: DelegatedType -> String
show_delegated_type_definition declaration = agda_name (delegated_type_name declaration) ++ foldl (++) "" (map (" " ++) $ delegated_type_parameters declaration) ++ " = " ++ show_type (delegated_type_delegation declaration)

show_delegated_type :: DelegatedType -> String
show_delegated_type declaration = join [show_delegated_type_signature declaration, show_delegated_type_definition declaration]

show_type_declaration :: TypeDeclaration -> String
show_type_declaration (Datatype declaration) = show_datatype declaration
show_type_declaration (RecordType declaration) = show_record_type declaration
show_type_declaration (DelegatedType declaration) = show_delegated_type declaration

show_type_declaration_signature :: TypeDeclaration -> String
show_type_declaration_signature (Datatype declaration) = show_datatype_signature declaration
show_type_declaration_signature (RecordType declaration) = show_record_type_signature declaration
show_type_declaration_signature (DelegatedType declaration) = show_delegated_type_signature declaration

show_type_declaration_definition :: TypeDeclaration -> String
show_type_declaration_definition (Datatype declaration) = show_datatype_definition declaration
show_type_declaration_definition (RecordType declaration) = show_record_type_definition declaration
show_type_declaration_definition (DelegatedType declaration) = show_delegated_type_definition declaration

show_type_declaration_group :: [TypeDeclaration] -> String
show_type_declaration_group [] = ""
show_type_declaration_group [declaration] = show_type_declaration declaration
show_type_declaration_group declarations =
	join2
	[
		join $ map show_type_declaration_signature declarations,
		join2 $ map show_type_declaration_definition declarations
	]

show_type_declarations :: [TypeDeclaration] -> String
show_type_declarations declarations = join2 $ map show_type_declaration_group (organize declarations)
