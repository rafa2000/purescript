-----------------------------------------------------------------------------
--
-- Module      :  Language.PureScript.CodeGen.JS
-- Copyright   :  (c) Phil Freeman 2013
-- License     :  MIT
--
-- Maintainer  :  Phil Freeman <paf31@cantab.net>
-- Stability   :  experimental
-- Portability :
--
-- |
-- This module generates code in the simplified Javascript intermediate representation from Purescript code
--
-----------------------------------------------------------------------------

{-# LANGUAGE DoAndIfThenElse #-}

module Language.PureScript.CodeGen.JS (
    module AST,
    ModuleType(..),
    CodeGenEnvironment(..),
    emptyCodeGenEnvironment,
    declToJs,
    moduleToJs,
    isIdent
) where

import Data.Maybe (catMaybes, fromJust, fromMaybe)
import Data.Function (on)
import Data.List (nub, (\\))

import Control.Monad.State
import Control.Applicative

import qualified Data.Map as M

import Language.PureScript.Names
import Language.PureScript.Declarations
import Language.PureScript.Options
import Language.PureScript.CodeGen.JS.AST as AST
import Language.PureScript.Types
import Language.PureScript.Optimizer
import Language.PureScript.CodeGen.Common
import Language.PureScript.Environment
import Language.PureScript.Supply
import Language.PureScript.Traversals (sndM)

-- |
-- Different types of modules which are supported
--
data ModuleType = CommonJS | Globals

data CodeGenEnvironment = CodeGenEnvironment
  {
    -- |
    -- Set of function names which have been uncurried during code generation
    --
    codeGenUncurriedFunctions :: M.Map (ModuleName, Ident) Int
  }

emptyCodeGenEnvironment :: CodeGenEnvironment
emptyCodeGenEnvironment = CodeGenEnvironment M.empty

-- |
-- Generate code in the simplified Javascript intermediate representation for all declarations in a
-- module.
--
moduleToJs :: (Functor m, Applicative m, Monad m) => ModuleType -> Options -> Module -> Environment -> StateT CodeGenEnvironment (SupplyT m) [JS]
moduleToJs mt opts (Module name decls (Just exps)) env = StateT $ \cgEnv -> do
  let jsImports = map (importToJs mt opts) . (\\ [name]) . nub $ concatMap imports decls
  let cgEnv' = extendCodeGenEnvironment name decls cgEnv
  jsDecls <- mapM (\decl -> declToJs opts name decl env cgEnv') decls
  let optimized = concat $ map (map $ optimize opts) $ catMaybes jsDecls
  let isModuleEmpty = null optimized
  let moduleBody = JSStringLiteral "use strict" : jsImports ++ optimized
  let moduleExports = JSObjectLiteral [ (runIdent expName, var expName) | ex <- exps, expName <- exportToJs name cgEnv' ex ]
  return ((case mt of
    CommonJS -> moduleBody ++ [JSAssignment (JSAccessor "exports" (JSVar "module")) moduleExports]
    Globals | not isModuleEmpty ->
      [ JSVariableIntroduction (fromJust (optionsBrowserNamespace opts))
                               (Just (JSBinary Or (JSVar (fromJust (optionsBrowserNamespace opts))) (JSObjectLiteral [])) )
      , JSAssignment (JSAccessor (moduleNameToJs name) (JSVar (fromJust (optionsBrowserNamespace opts))))
                     (JSApp (JSFunction Nothing [] (JSBlock (moduleBody ++ [JSReturn moduleExports]))) [])
      ]
    _ -> []), cgEnv')
moduleToJs _ _ _ _ = error "Exports should have been elaborated in name desugaring"

extendCodeGenEnvironment :: ModuleName -> [Declaration] -> CodeGenEnvironment -> CodeGenEnvironment
extendCodeGenEnvironment mn ds env = foldl go env ds
  where
  go :: CodeGenEnvironment -> Declaration -> CodeGenEnvironment
  go cgEnv (ValueDeclaration ident _ _ _ val) = handleValue cgEnv ident val
  go cgEnv (BindingGroupDeclaration vals) = foldl (\e (ident, _, val) -> handleValue e ident val) cgEnv vals
  go cgEnv (PositionedDeclaration _ d) = go cgEnv d
  go cgEnv _ = cgEnv

  handleValue :: CodeGenEnvironment -> Ident -> Value -> CodeGenEnvironment
  handleValue cgEnv ident val =
    case extractFunctionArguments val of
      (args, _) | length args > 1 -> cgEnv { codeGenUncurriedFunctions = M.insert (mn, ident) (length args) (codeGenUncurriedFunctions cgEnv)  }
      _ -> cgEnv

importToJs :: ModuleType -> Options -> ModuleName -> JS
importToJs mt opts mn = JSVariableIntroduction (moduleNameToJs mn) (Just moduleBody)
  where
  moduleBody = case mt of
    CommonJS -> JSApp (JSVar "require") [JSStringLiteral (runModuleName mn)]
    Globals -> JSAccessor (moduleNameToJs mn) (JSVar (fromJust (optionsBrowserNamespace opts)))

imports :: Declaration -> [ModuleName]
imports =
  let (f, _, _, _, _) = everythingOnValues (++) (const []) collect (const []) (const []) (const [])
  in f
  where
  collect :: Value -> [ModuleName]
  collect (Var (Qualified (Just mn) _)) = [mn]
  collect (Constructor (Qualified (Just mn) _)) = [mn]
  collect _ = []

-- |
-- Generate code in the simplified Javascript intermediate representation for a declaration
--
declToJs :: (Functor m, Applicative m, Monad m) => Options -> ModuleName -> Declaration -> Environment -> CodeGenEnvironment -> SupplyT m (Maybe [JS])
declToJs opts mp (ValueDeclaration ident _ _ _ val) e cgEnv = do
  jss <- valueDeclToJs opts mp e cgEnv ident val
  return $ Just jss
declToJs opts mp (BindingGroupDeclaration vals) e cgEnv = do
  jss <- forM vals $ \(ident, _, val) -> valueDeclToJs opts mp e cgEnv ident val
  return $ Just (concat jss)
declToJs _ mp (DataDeclaration _ _ ctors) _ _ = do
  return $ Just $ flip concatMap ctors $ \(pn@(ProperName ctor), tys) ->
    [JSVariableIntroduction ctor (Just (go pn 0 tys []))]
    where
    go :: ProperName -> Integer -> [Type] -> [JS] -> JS
    go pn _ [] values =
      JSObjectLiteral [ ("ctor", JSStringLiteral (show (Qualified (Just mp) pn))), ("values", JSArrayLiteral $ reverse values) ]
    go pn index (_ : tys') values =
      JSFunction Nothing ["value" ++ show index]
        (JSBlock [JSReturn (go pn (index + 1) tys' (JSVar ("value" ++ show index) : values))])
declToJs opts mp (DataBindingGroupDeclaration ds) e cgEnv = do
  jss <- mapM (\decl -> declToJs opts mp decl e cgEnv) ds
  return $ Just $ concat $ catMaybes jss
declToJs _ _ (ExternDeclaration _ _ (Just js) _) _ _ = return $ Just [js]
declToJs opts mp (PositionedDeclaration _ d) e cgEnv = declToJs opts mp d e cgEnv
declToJs _ _ _ _ _ = return Nothing

valueDeclToJs :: (Functor m, Applicative m, Monad m) => Options -> ModuleName -> Environment -> CodeGenEnvironment -> Ident -> Value -> SupplyT m [JS]
valueDeclToJs opts mp e cgEnv ident val =
  case extractFunctionArguments val of
    (args, val') | length args > 1 -> curriedDeclarationToJs ident opts mp e cgEnv args val'
    _ -> do
      js <- valueToJs opts mp e cgEnv val
      return [JSVariableIntroduction (identToJs ident) (Just js)]

-- |
-- Pull all of the function abstractions off the front of a value
--
extractFunctionArguments :: Value -> ([Ident], Value)
extractFunctionArguments = go []
  where
  go acc (Abs (Left ident) result) = go (ident : acc) result
  go _   (Abs (Right _) _) = error "Binder was not desugared in extractFunctionArguments"
  go acc (TypedValue _ val _) = go acc val
  go acc (PositionedValue _ val) = go acc val
  go acc other = (reverse acc, other)

curriedDeclarationToJs :: (Functor m, Applicative m, Monad m) => Ident -> Options -> ModuleName -> Environment -> CodeGenEnvironment -> [Ident] -> Value -> SupplyT m [JS]
curriedDeclarationToJs ident opts mp e cgEnv args val = do
  js <- valueToJs opts mp e cgEnv val
  let
    uncurried :: JS
    uncurried = JSFunction Nothing (map identToJs args) (JSBlock [JSReturn js])

    curried :: JS
    curried = foldr (\arg ret -> JSFunction Nothing [identToJs arg] (JSBlock [JSReturn ret])) applyUncurried args

    applyUncurried :: JS
    applyUncurried = JSApp (JSVar (identToJs (uncurriedName ident))) [JSVar (identToJs arg) | arg <- args]
  return [ JSVariableIntroduction (identToJs (uncurriedName ident)) (Just uncurried)
         , JSVariableIntroduction (identToJs ident) (Just curried)
         ]

uncurriedName :: Ident -> Ident
uncurriedName ident = Ident ("__uncurried_" ++ identToJs ident)

-- |
-- Generate key//value pairs for an object literal exporting values from a module.
--
exportToJs :: ModuleName -> CodeGenEnvironment -> DeclarationRef -> [Ident]
exportToJs _ _ (TypeRef _ (Just dctors)) = map (Ident . runProperName) dctors
exportToJs mn cgEnv (ValueRef name) | M.member (mn, name) (codeGenUncurriedFunctions cgEnv) = [name, uncurriedName name]
                                    | otherwise = [name]
exportToJs mn cgEnv (TypeInstanceRef name) | M.member (mn, name) (codeGenUncurriedFunctions cgEnv) = [name, uncurriedName name]
                                           | otherwise = [name]
exportToJs _ _ _ = []

-- |
-- Generate code in the simplified Javascript intermediate representation for a variable based on a
-- PureScript identifier.
--
var :: Ident -> JS
var = JSVar . identToJs

-- |
-- Generate code in the simplified Javascript intermediate representation for an accessor based on
-- a PureScript identifier. If the name is not valid in Javascript (symbol based, reserved name) an
-- indexer is returned.
--
accessor :: Ident -> JS -> JS
accessor (Ident prop) = accessorString prop
accessor (Op op) = JSIndexer (JSStringLiteral op)

accessorString :: String -> JS -> JS
accessorString prop | isIdent prop = JSAccessor prop
                    | otherwise = JSIndexer (JSStringLiteral prop)

-- |
-- Generate code in the simplified Javascript intermediate representation for a value or expression.
--
valueToJs :: (Functor m, Applicative m, Monad m) => Options -> ModuleName -> Environment -> CodeGenEnvironment -> Value -> SupplyT m JS
valueToJs _    _ _ _     (NumericLiteral n) = return $ JSNumericLiteral n
valueToJs _    _ _ _     (StringLiteral s) = return $ JSStringLiteral s
valueToJs _    _ _ _     (BooleanLiteral b) = return $ JSBooleanLiteral b
valueToJs opts m e cgEnv (ArrayLiteral xs) = JSArrayLiteral <$> mapM (valueToJs opts m e cgEnv) xs
valueToJs opts m e cgEnv (ObjectLiteral ps) = JSObjectLiteral <$> mapM (sndM (valueToJs opts m e cgEnv)) ps
valueToJs opts m e cgEnv (ObjectUpdate o ps) = do
  obj <- valueToJs opts m e cgEnv o
  sts <- mapM (sndM (valueToJs opts m e cgEnv)) ps
  extendObj obj sts
valueToJs _    m _ _     (Constructor name) = return $ qualifiedToJS m (Ident . runProperName) name
valueToJs opts m e cgEnv (Case values binders) = do
  vals <- mapM (valueToJs opts m e cgEnv) values
  bindersToJs opts m e cgEnv binders vals
valueToJs opts m e cgEnv (IfThenElse cond th el) = JSConditional <$> valueToJs opts m e cgEnv cond <*> valueToJs opts m e cgEnv th <*> valueToJs opts m e cgEnv el
valueToJs opts m e cgEnv (Accessor prop val) = accessorString prop <$> valueToJs opts m e cgEnv val
valueToJs opts m e cgEnv app@(App fn arg) =
  case canUncurry m cgEnv app of
    Just (Qualified mn fnName, args) -> appToJs opts m e cgEnv (Var (Qualified mn (uncurriedName fnName))) args
    Nothing -> appToJs opts m e cgEnv fn [arg]
valueToJs opts m e cgEnv (Let ds val) = do
  let cgEnv' = extendCodeGenEnvironment m ds cgEnv
  decls <- concat . catMaybes <$> mapM (\d -> declToJs opts m d e cgEnv') ds
  ret <- valueToJs opts m e cgEnv' val
  return $ JSApp (JSFunction Nothing [] (JSBlock (decls ++ [JSReturn ret]))) []
valueToJs opts m e cgEnv (Abs (Left arg) val) = do
  ret <- valueToJs opts m e cgEnv val
  return $ JSFunction Nothing [identToJs arg] (JSBlock [JSReturn ret])
valueToJs opts m e cgEnv (TypedValue _ (Abs (Left arg) val) ty) | optionsPerformRuntimeTypeChecks opts = do
  let arg' = identToJs arg
  ret <- valueToJs opts m e cgEnv val
  return $ JSFunction Nothing [arg'] (JSBlock $ runtimeTypeChecks arg' ty ++ [JSReturn ret])
valueToJs _    m _ _     (Var ident) = return $ varToJs m ident
valueToJs opts m e cgEnv (TypedValue _ val _) = valueToJs opts m e cgEnv val
valueToJs opts m e cgEnv (PositionedValue _ val) = valueToJs opts m e cgEnv val
valueToJs _    _ _ _     (TypeClassDictionary _ _ _) = error "Type class dictionary was not replaced"
valueToJs _    _ _ _     _ = error "Invalid argument to valueToJs"

canUncurry :: ModuleName -> CodeGenEnvironment -> Value -> Maybe (Qualified Ident, [Value])
canUncurry mn cgEnv app =
  let
    extract acc (App fn arg) = extract (arg : acc) fn
    extract acc (TypedValue _ val _) = extract acc val
    extract acc (PositionedValue _ val) = extract acc val
    extract acc other = (other, acc)

    varName (Var name) = Just name
    varName (TypedValue _ val _) = varName val
    varName (PositionedValue _ val) = varName val
    varName _ = Nothing

    (lhs, args) = extract [] app

    fnNameAndArgs = case varName lhs of
      Just name | M.lookup (qualify mn name) (codeGenUncurriedFunctions cgEnv) == Just (length args) -> Just (name, args)
      _ -> Nothing
  in fnNameAndArgs

appToJs :: (Functor m, Applicative m, Monad m) => Options -> ModuleName -> Environment -> CodeGenEnvironment -> Value -> [Value] -> SupplyT m JS
appToJs opts m e cgEnv fn args = JSApp <$> valueToJs opts m e cgEnv fn <*> mapM (valueToJs opts m e cgEnv) args

-- |
-- Shallow copy an object.
--
extendObj :: (Functor m, Applicative m, Monad m) => JS -> [(String, JS)] -> SupplyT m JS
extendObj obj sts = do
  newObj <- freshName
  key <- freshName
  let
    jsKey = JSVar key
    jsNewObj = JSVar newObj
    block = JSBlock (objAssign:copy:extend ++ [JSReturn jsNewObj])
    objAssign = JSVariableIntroduction newObj (Just $ JSObjectLiteral [])
    copy = JSForIn key obj $ JSBlock [JSIfElse cond assign Nothing]
    cond = JSApp (JSAccessor "hasOwnProperty" obj) [jsKey]
    assign = JSBlock [JSAssignment (JSIndexer jsKey jsNewObj) (JSIndexer jsKey obj)]
    stToAssign (s, js) = JSAssignment (JSAccessor s jsNewObj) js
    extend = map stToAssign sts
  return $ JSApp (JSFunction Nothing [] block) []

-- |
-- Generate code in the simplified Javascript intermediate representation for runtime type checks.
--
runtimeTypeChecks :: String -> Type -> [JS]
runtimeTypeChecks arg ty =
  let
    argTy = getFunctionArgumentType ty
  in
    maybe [] (argumentCheck (JSVar arg)) argTy
  where
  getFunctionArgumentType :: Type -> Maybe Type
  getFunctionArgumentType (TypeApp (TypeApp t funArg) _) | t == tyFunction = Just funArg
  getFunctionArgumentType (ForAll _ ty' _) = getFunctionArgumentType ty'
  getFunctionArgumentType _ = Nothing
  argumentCheck :: JS -> Type -> [JS]
  argumentCheck val t | t == tyNumber = [typeCheck val "number"]
  argumentCheck val t | t == tyString = [typeCheck val "string"]
  argumentCheck val t | t == tyBoolean = [typeCheck val "boolean"]
  argumentCheck val (TypeApp t _) | t == tyArray = [arrayCheck val]
  argumentCheck val (TypeApp t row) | t == tyObject =
    let
      (pairs, _) = rowToList row
    in
      typeCheck val "object" : concatMap (\(prop, ty') -> argumentCheck (accessorString prop val) ty') pairs
  argumentCheck val (TypeApp (TypeApp t _) _) | t == tyFunction = [typeCheck val "function"]
  argumentCheck val (ForAll _ ty' _) = argumentCheck val ty'
  argumentCheck _ _ = []
  typeCheck :: JS -> String -> JS
  typeCheck js ty' = JSIfElse (JSBinary NotEqualTo (JSTypeOf js) (JSStringLiteral ty')) (JSBlock [JSThrow (JSStringLiteral $ ty' ++ " expected")]) Nothing
  arrayCheck :: JS -> JS
  arrayCheck js = JSIfElse (JSUnary Not (JSApp (JSAccessor "isArray" (JSVar "Array")) [js])) (JSBlock [JSThrow (JSStringLiteral "Array expected")]) Nothing

-- |
-- Generate code in the simplified Javascript intermediate representation for a reference to a
-- variable.
--
varToJs :: ModuleName -> Qualified Ident -> JS
varToJs _ (Qualified Nothing ident) = var ident
varToJs m qual = qualifiedToJS m id qual

-- |
-- Generate code in the simplified Javascript intermediate representation for a reference to a
-- variable that may have a qualified name.
--
qualifiedToJS :: ModuleName -> (a -> Ident) -> Qualified a -> JS
qualifiedToJS m f (Qualified (Just m') a) | m /= m' = accessor (f a) (JSVar (moduleNameToJs m'))
qualifiedToJS _ f (Qualified _ a) = JSVar $ identToJs (f a)

-- |
-- Generate code in the simplified Javascript intermediate representation for pattern match binders
-- and guards.
--
bindersToJs :: (Functor m, Applicative m, Monad m) => Options -> ModuleName -> Environment -> CodeGenEnvironment -> [CaseAlternative] -> [JS] -> SupplyT m JS
bindersToJs opts m e cgEnv binders vals = do
  valNames <- replicateM (length vals) freshName
  jss <- forM binders $ \(CaseAlternative bs grd result) -> do
    ret <- valueToJs opts m e cgEnv result
    go valNames [JSReturn ret] bs grd
  return $ JSApp (JSFunction Nothing valNames (JSBlock (concat jss ++ [JSThrow (JSStringLiteral "Failed pattern match")])))
                 vals
  where
    go :: (Functor m, Applicative m, Monad m) => [String] -> [JS] -> [Binder] -> Maybe Guard -> SupplyT m [JS]
    go _ done [] Nothing = return done
    go _ done [] (Just cond) = do
      cond' <- valueToJs opts m e cgEnv cond
      return [JSIfElse cond' (JSBlock done) Nothing]
    go (v:vs) done' (b:bs) grd = do
      done'' <- go vs done' bs grd
      binderToJs m e cgEnv v done'' b
    go _ _ _ _ = error "Invalid arguments to bindersToJs"

-- |
-- Generate code in the simplified Javascript intermediate representation for a pattern match
-- binder.
--
binderToJs :: (Functor m, Applicative m, Monad m) => ModuleName -> Environment -> CodeGenEnvironment -> String -> [JS] -> Binder -> SupplyT m [JS]
binderToJs _ _ _ _ done NullBinder = return done
binderToJs _ _ _ varName done (StringBinder str) =
  return [JSIfElse (JSBinary EqualTo (JSVar varName) (JSStringLiteral str)) (JSBlock done) Nothing]
binderToJs _ _ _ varName done (NumberBinder num) =
  return [JSIfElse (JSBinary EqualTo (JSVar varName) (JSNumericLiteral num)) (JSBlock done) Nothing]
binderToJs _ _ _ varName done (BooleanBinder True) =
  return [JSIfElse (JSVar varName) (JSBlock done) Nothing]
binderToJs _ _ _ varName done (BooleanBinder False) =
  return [JSIfElse (JSUnary Not (JSVar varName)) (JSBlock done) Nothing]
binderToJs _ _ _ varName done (VarBinder ident) =
  return (JSVariableIntroduction (identToJs ident) (Just (JSVar varName)) : done)
binderToJs m e cgEnv varName done (ConstructorBinder ctor bs) = do
  js <- go 0 done bs
  if isOnlyConstructor e ctor
  then
    return js
  else
    return [JSIfElse (JSBinary EqualTo (JSAccessor "ctor" (JSVar varName)) (JSStringLiteral (show ctor)))
                     (JSBlock js)
                     Nothing]
  where
  go :: (Functor m, Applicative m, Monad m) => Integer -> [JS] -> [Binder] -> SupplyT m [JS]
  go _ done' [] = return done'
  go index done' (binder:bs') = do
    argVar <- freshName
    done'' <- go (index + 1) done' bs'
    js <- binderToJs m e cgEnv argVar done'' binder
    return (JSVariableIntroduction argVar (Just (JSIndexer (JSNumericLiteral (Left index)) (JSAccessor "values" (JSVar varName)))) : js)
binderToJs m e cgEnv varName done (ObjectBinder bs) = go done bs
  where
  go :: (Functor m, Applicative m, Monad m) => [JS] -> [(String, Binder)] -> SupplyT m [JS]
  go done' [] = return done'
  go done' ((prop, binder):bs') = do
    propVar <- freshName
    done'' <- go done' bs'
    js <- binderToJs m e cgEnv propVar done'' binder
    return (JSVariableIntroduction propVar (Just (accessorString prop (JSVar varName))) : js)
binderToJs m e cgEnv varName done (ArrayBinder bs) = do
  js <- go done 0 bs
  return [JSIfElse (JSBinary EqualTo (JSAccessor "length" (JSVar varName)) (JSNumericLiteral (Left (fromIntegral $ length bs)))) (JSBlock js) Nothing]
  where
  go :: (Functor m, Applicative m, Monad m) => [JS] -> Integer -> [Binder] -> SupplyT m [JS]
  go done' _ [] = return done'
  go done' index (binder:bs') = do
    elVar <- freshName
    done'' <- go done' (index + 1) bs'
    js <- binderToJs m e cgEnv elVar done'' binder
    return (JSVariableIntroduction elVar (Just (JSIndexer (JSNumericLiteral (Left index)) (JSVar varName))) : js)
binderToJs m e cgEnv varName done (ConsBinder headBinder tailBinder) = do
  headVar <- freshName
  tailVar <- freshName
  js1 <- binderToJs m e cgEnv headVar done headBinder
  js2 <- binderToJs m e cgEnv tailVar js1 tailBinder
  return [JSIfElse (JSBinary GreaterThan (JSAccessor "length" (JSVar varName)) (JSNumericLiteral (Left 0))) (JSBlock
    ( JSVariableIntroduction headVar (Just (JSIndexer (JSNumericLiteral (Left 0)) (JSVar varName))) :
      JSVariableIntroduction tailVar (Just (JSApp (JSAccessor "slice" (JSVar varName)) [JSNumericLiteral (Left 1)])) :
      js2
    )) Nothing]
binderToJs m e cgEnv varName done (NamedBinder ident binder) = do
  js <- binderToJs m e cgEnv varName done binder
  return (JSVariableIntroduction (identToJs ident) (Just (JSVar varName)) : js)
binderToJs m e cgEnv varName done (PositionedBinder _ binder) =
  binderToJs m e cgEnv varName done binder

-- |
-- Checks whether a data constructor is the only constructor for that type, used to simplify the
-- check when generating code for binders.
--
isOnlyConstructor :: Environment -> Qualified ProperName -> Bool
isOnlyConstructor e ctor =
  let ty = fromMaybe (error "Data constructor not found") $ ctor `M.lookup` dataConstructors e
  in numConstructors (ctor, ty) == 1
  where
  numConstructors ty = length $ filter (((==) `on` typeConstructor) ty) $ M.toList $ dataConstructors e
  typeConstructor (Qualified (Just moduleName) _, (tyCtor, _)) = (moduleName, tyCtor)
  typeConstructor _ = error "Invalid argument to isOnlyConstructor"

