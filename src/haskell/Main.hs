module Main (main) where

import GHC
	(
		runGhc,
		getSessionDynFlags,
		setSessionDynFlags,
		modInfoExports,
		lookupName,
		getModuleInfo,
		moduleNameString,
		moduleNameString,
		moduleName,
		mkModule,
		TyThing (AnId, AConLike, ATyCon, ACoAxiom),
		nameModule,
		getName,
		Ghc,
		idType,
		isClassTyCon,
		TyVar,
		tyConTyVars,
		dataConFieldLabels,
		DynFlags,
		DataCon
	)
import GHC.Paths (libdir)
import Packages
	(
		listPackageConfigMap,
		exposedModules,
		PackageName (PackageName),
		packageName,
		unitId,
		PackageConfig
	)
import Module (DefUnitId (DefUnitId), UnitId (DefiniteUnitId))
import Data.Traversable (for)
import FastString (unpackFS)
import Control.Monad.IO.Class (liftIO)
import System.IO (openFile, IOMode (WriteMode), hPutStrLn, hFlush)
import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeDirectory)
import Data.Map (fromListWith)
import qualified Data.Map as Map
import Var (varType, ArgFlag(Specified, Required), TyVarBndr (TvBndr))
import Data.Maybe (fromMaybe, mapMaybe)
import XXXX.SourceCode
	(
		Module (Module),
		Datatype (Data),
		Function (Function),
		Type (Application, ForAll, Named),
		module_name,
		module_types,
		module_functions,
		module_reexports,
		module_postulated_types,
		function_name,
		function_type,
		show_module,
		Visibility (Inferred, Instance, Explicit),
		name_string,
		name_fixity,
		name_is_operator,
		Name (Name),
		TypeDeclaration (Datatype, RecordType, DelegatedType),
		Datatype (Data),
		datatype_name,
		datatype_type,
		datatype_parameters,
		datatype_constructors,
		RecordType (Record),
		record_type_name,
		record_type_fields,
		record_type_parameters,
		DelegatedType (Delegate),
		delegated_type_name,
		delegated_type_delegation,
		delegated_type_type,
		delegated_type_parameters
	)
import qualified GHC
import Data.Foldable (for_)
import qualified TyCoRep
import qualified Var
import Name (getOccString, isSymOcc, nameOccName, occNameString, nameModule_maybe)
import TyCon
	(
		tyConName,
		AlgTyConRhs (AbstractTyCon, DataTyCon, NewTyCon),
		algTyConRhs,
		data_cons,
		data_con,
		nt_rhs,
		isAlgTyCon,
		tyConKind,
		tyConResKind
	)
import PrelNames (tYPETyConKey, getUnique, runtimeRepTyConKey, constraintKindTyConKey)
import Data.List (partition)
import DataCon (dataConInstSig, flSelector, dataConFieldType, flLabel)

data TyThingStyle =
	Id |
	ConLike |
	TyCon |
	CoAxiom
	deriving (Eq, Ord)

name_to_type :: [GHC.Name] -> GHC.Name -> Type
name_to_type bound name =
	let n = getOccString name in
	case nameModule_maybe name of
		Nothing -> Named "" n
		Just m -> Named (moduleNameString $ moduleName m) n

internalize_visibility :: ArgFlag -> Visibility
internalize_visibility Var.Inferred = Inferred
internalize_visibility Specified = Inferred
internalize_visibility Required = Explicit

universe :: Type
universe = Named "" "Set \x2113"

internalize_type :: [GHC.Name] -> GHC.Type -> Type
internalize_type bound ty = case ty of
	TyCoRep.TyVarTy var -> name_to_type bound $ getName var
	TyCoRep.AppTy t1 t2 -> Application (internalize_type bound t1) (internalize_type bound t2)
	TyCoRep.TyConApp tycon args ->
		if elem (getUnique tycon) [tYPETyConKey, constraintKindTyConKey]
		then universe
		else foldl Application (name_to_type bound $ tyConName tycon) (map (internalize_type bound) args)
	TyCoRep.ForAllTy (TvBndr var _) t | ignore (varType var) -> internalize_type bound t
		where
		ignore (TyCoRep.TyConApp tycon _) = getUnique tycon == runtimeRepTyConKey
		ignore _ = False
	TyCoRep.ForAllTy (TvBndr var flag) t -> ForAll (internalize_visibility flag) (getOccString var) (internalize_type bound $ varType var) $ internalize_type (getName var : bound) t
	TyCoRep.FunTy l@(TyCoRep.TyConApp tycon _) r | isClassTyCon tycon -> ForAll Instance "_" (internalize_type bound l) (internalize_type bound r)
	TyCoRep.FunTy l r -> ForAll Explicit "_" (internalize_type bound l) (internalize_type bound r)
	_ -> Named "" "_"

get_functions :: DynFlags -> [TyThing] -> Ghc [Function]
get_functions flags tyths =
	for tyths $ \ (AnId id) -> do
		let occ = nameOccName (getName id)
		let name = occNameString occ
		liftIO . putStrLn $ "      \x2022 Looking at function " ++ name
		let is_operator = isSymOcc occ
		let ty = internalize_type [] (idType id)
		return
			Function
			{
				function_name = Name
				{
					name_string = name,
					name_fixity = Nothing,
					name_is_operator = is_operator
				},
				function_type = ty
			}

internalize_signature :: GHC.Type -> [GHC.Name] -> ([TyVar], [GHC.Type], [GHC.Type]) -> Type
internalize_signature result bound (inferred, instance', explicit) =
	foldr internalize_inferred (foldr internalize_instance (foldr internalize_explicit (internalize_type bound result) explicit) instance') inferred
	where
	internalize_inferred l = ForAll Inferred (getOccString l) (internalize_type bound $ TyCoRep.mkTyVarTy l)
	internalize_instance l = ForAll Instance "_" (internalize_type bound l)
	internalize_explicit l = ForAll Explicit "_" (internalize_type bound l)

internalize_field :: [GHC.Name] -> GHC.Name -> GHC.Type -> Function
internalize_field bound field ty =
	Function
	{
		function_name = Name
		{
			name_string = name,
			name_fixity = Nothing,
			name_is_operator = is_operator
		},
		function_type = internalize_type bound ty
	}
	where
	occ = nameOccName field
	name = occNameString occ
	is_operator = isSymOcc occ

internalize_constructor :: [TyVar] -> GHC.Type -> [GHC.Name] -> DataCon -> Either Function RecordType
internalize_constructor universals result bound con =
	case dataConFieldLabels con of
		[] ->
			Left Function
			{
				function_name = name,
				function_type = internalize_signature result bound $ dataConInstSig con (TyCoRep.mkTyVarTys universals)
			}
		labels ->
			Right Record
			{
				record_type_name = name,
				record_type_fields = map (\ label -> internalize_field bound (flSelector label) (dataConFieldType con (flLabel label))) labels,
				record_type_parameters = map (internalize_parameter bound) universals
			}
	where
	occ = nameOccName (getName con)
	name_string = occNameString occ
	is_operator = isSymOcc occ
	name =
		Name
		{
			name_string = name_string,
			name_fixity = Nothing,
			name_is_operator = is_operator
		}

internalize_parameter :: [GHC.Name] -> TyVar -> (Visibility, String, Type)
internalize_parameter bound var = (Explicit, getOccString var, internalize_type bound $ varType var)

get_types :: DynFlags -> [TyThing] -> Ghc ([Function], [TypeDeclaration])
get_types flags tyths = do
	eithers <- for tyths $ \ (ATyCon con) ->
		if not (isAlgTyCon con)
		then return Nothing
		else do
			let occ = nameOccName (getName con)
			let name_string = occNameString occ
			liftIO . putStrLn $ "      \x2022 Looking at type " ++ name_string
			let is_operator = isSymOcc occ
			let name =
				Name
				{
					name_string = name_string,
					name_fixity = Nothing,
					name_is_operator = is_operator
				}
			let vars = tyConTyVars con
			let bound = map getName vars
			let ty = tyConResKind con
			let full_ty = tyConKind con
			return . Just $ case algTyConRhs con of
				AbstractTyCon ->
					Left $ Function
					{
						function_name = name,
						function_type = internalize_type [] ty
					}
				DataTyCon {data_cons = cons} ->
					-- Either Function (RecordType, ())
					case map (internalize_constructor vars ty bound) cons of
						[Right declaration] -> Right [RecordType declaration]
						internalized_constructors ->
							Right . (: map RecordType ts) $ Datatype Data
							{
								datatype_name = name,
								datatype_type = internalize_type [] ty,
								datatype_parameters = map (internalize_parameter bound) vars,
								datatype_constructors = constructors
							}
							where
							g (Left f) (fs, ts) = (f : fs, ts)
							g (Right t) (fs, ts) = (fs, t : ts)
							(fs, ts) = foldr g ([], []) internalized_constructors
							contructor_from_record t =
								Function
								{
									function_name = record_type_name t,
									function_type = foldl Application
										(Named (moduleNameString . moduleName . nameModule $ getName con) (XXXX.SourceCode.name_string $ record_type_name t))
										$ map (internalize_type bound) (TyCoRep.mkTyVarTys vars)
								}
							constructors = fs ++ map contructor_from_record ts
				NewTyCon {data_con = dcon, nt_rhs = rhs} ->
					Right . (: []) $ DelegatedType Delegate
					{
						delegated_type_name = name,
						delegated_type_delegation = internalize_type bound rhs,
						delegated_type_type = internalize_type [] full_ty,
						delegated_type_parameters = map getOccString vars
					}
				_ ->
					Right . (: []) $ DelegatedType Delegate
					{
						delegated_type_name = name,
						delegated_type_delegation = Named "" "_",
						delegated_type_type = Named "" "_",
						delegated_type_parameters = []
					}
	return $ foldr (\ which (fs, ts) -> case which of Just (Left f) -> (f : fs, ts); Just (Right t) -> (fs, t ++ ts); Nothing -> (fs, ts)) ([], []) eithers

get_modules :: DynFlags -> PackageConfig -> Ghc [Module]
get_modules flags package = (>>= return . mapMaybe id) $
	for (exposedModules package) $ \ (mname, _) -> do
		let name = moduleNameString mname
		liftIO . putStr $ "   \x2022 Looking at module " ++ name
		let mod = mkModule (DefiniteUnitId $ DefUnitId (unitId package)) mname
		maybe_info <- getModuleInfo mod
		case maybe_info of
			Nothing -> liftIO (putStrLn " [Not Found]") >> return Nothing
			Just info -> (>>= return . Just) $ do
				liftIO $ putStrLn ""
				let x = modInfoExports info
				all_ex <- mapM lookupName x
				let (ex, _) = partition ((mod ==) . nameModule . fst) (zip x all_ex)
				let exports = ($ ex) $ fromListWith (++) . map ((. snd) $ \ (Just tyth) -> (case tyth of AnId _ -> Id ; AConLike _ -> ConLike ; ATyCon _ -> TyCon ; ACoAxiom _ -> CoAxiom, [tyth]))
				functions <- get_functions flags $ fromMaybe [] $ Map.lookup Id exports
				(postulated_types, types) <- get_types flags $ fromMaybe [] $ Map.lookup TyCon exports
				return
					Module
					{
						module_name = name,
						module_functions = functions,
						module_types = types,
						module_reexports = Map.empty,
						module_postulated_types = postulated_types
					}

data Package =
	Package
	{
		package_name :: String,
		package_modules :: [Module]
	}

get_packages :: DynFlags -> Ghc [Package]
get_packages flags =
	for (listPackageConfigMap flags) $ \ package -> do
		let name = unpackFS $ case packageName package of PackageName name -> name
		liftIO . putStrLn $ "\x2022 Looking at package " ++ name
		modules <- get_modules flags package
		return Package { package_name = name, package_modules = modules }

pretty, pretty_noln :: String -> IO ()
pretty_noln line = do
	putStrLn ""
	putStrLn line
	putStrLn "--~~==~~--"
pretty line = pretty_noln line >> putStrLn ""

generate_package :: Package -> IO ()
generate_package package =
	for_ (package_modules package) $ \ mod -> do
		let filename = "xxxx/generated/agda/" ++ (package_name package) ++ "/" ++ (map (\ c -> case c of '.' -> '/' ; _ -> c) $ module_name mod) ++ ".agda"
		liftIO $ createDirectoryIfMissing True $ takeDirectory filename
		file <- openFile filename WriteMode
		putStrLn $ "   \x2022 Generating module " ++ (module_name mod)
		hPutStrLn file $ (show_module mod)
		hFlush file

generate_packages :: [Package] -> IO ()
generate_packages packages =
	for_ packages $ \ package -> do
		putStrLn $ "\x2022 Generating package " ++ (package_name package)
		generate_package package

main :: IO ()
main = do
	pretty "INSPECTING HASKELL FILES"
	packages <- runGhc (Just libdir) $ do
		setSessionDynFlags =<< getSessionDynFlags
		get_packages =<< getSessionDynFlags
	pretty "GENERATING AGDA FILES"
	generate_packages packages
	pretty_noln "DONE"
