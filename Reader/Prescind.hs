module Reader.Prescind where

---

import Data.Binding
import Data.Expression

import Data.Error
import Reader.Data
import Reader.Error
import qualified Reader.Parser.Data as PD

import Data.Maybe
import Control.Monad.State

import qualified Data.IntMap.Strict as IM
import qualified Data.StringMap as SM

---

type Prescinder a b = a -> StateT ST (Either Error) b

---

data ST = ST
  { count :: Int
  , tIndex :: SM.StringMap
  , tName :: NameTable
  , tPos :: PositionTable
  , tArgs :: ArgumentTable  
  }

---

prescind
  :: PD.Specification -> Either Error Specification

prescind spec = do
  evalStateT (pcSpec spec)
    ST { count = 0
       , tIndex = SM.empty
       , tName = IM.empty
       , tPos = IM.empty
       , tArgs = IM.empty
       }
             
---

pcSpec
  :: Prescinder PD.Specification Specification

pcSpec s = do
  mapM_ (\x -> add (bIdent x,bPos x)) $ PD.parameters s
  mapM_ (\x -> add (bIdent x,bPos x)) $ PD.definitions s
  ps <- mapM pcBind $ PD.parameters s 
  vs <- mapM pcBind $ PD.definitions s

  mapM_ (\x -> add (bIdent x,bPos x)) $ PD.inputs s
  mapM_ (\x -> add (bIdent x,bPos x)) $ PD.outputs s
  is <- mapM pcBind $ PD.inputs s
  os <- mapM pcBind $ PD.outputs s
  
  as <- mapM pcExpr $ PD.assumptions s
  bs <- mapM pcExpr $ PD.invariants s
  gs <- mapM pcExpr $ PD.guarantees s

  st <- get

  return $ Specification
    (PD.title s)
    (PD.description s)
    (PD.semantics s)
    (PD.target s)
    (PD.tags s)
    ps vs is os as bs gs
    IM.empty
    (tName st)
    (tPos st)
    (tArgs st)
    IM.empty
    IM.empty

---

pcBind
  :: Prescinder (Bind Expr String) (Bind Expr Int)

pcBind b = do
  a <- get
  as <- mapM add $ bArgs b
  es <- mapM pcExpr $ bVal b
  a' <- get
  i <- case SM.lookup (bIdent b) $ tIndex a of
    Just j  -> return j
    Nothing -> errUnknown (bIdent b) (bPos b)

  put $ a' {
    tIndex = tIndex a,
    tArgs = IM.insert i (map fst as) $ tArgs a'
    }  
    
  return Bind
    { bIdent = i
    , bArgs = as
    , bPos = bPos b              
    , bVal = es
    }
  
---

add
  :: Prescinder (String,ExprPos) (Int,ExprPos)

add (i,pos) = do
  a <- get
  case SM.lookup i $ tIndex a of
    Nothing -> do
      put ST
        { count = count a + 1
        , tIndex = SM.insert i (count a) $ tIndex a
        , tName = IM.insert (count a) i $ tName a
        , tPos = IM.insert (count a) pos $ tPos a
        , tArgs = IM.insert (count a) [] $ tArgs a         
        }
      return (count a,pos)
    Just j ->
      let Just p = IM.lookup j $ tPos a
      in errConflict i p pos

---

check
  :: Prescinder (String,ExprPos) (Int,ExprPos)

check (i,pos) = do
  a <- get
  case SM.lookup i $ tIndex a of
    Nothing -> errUnknown i pos
    Just j  -> return (j,pos)

---

pcExpr
  :: Prescinder (Expr String) (Expr Int)

pcExpr e = case expr e of
  BaseOtherwise    -> return $ Expr BaseOtherwise $ srcPos e
  BaseWild         -> return $ Expr BaseWild $ srcPos e
  BaseTrue         -> return $ Expr BaseTrue $ srcPos e
  BaseFalse        -> return $ Expr BaseFalse $ srcPos e
  BaseCon x        -> return $ Expr (BaseCon x) $ srcPos e
  BlnNot x         -> lift' BlnNot x
  NumSMin x        -> lift' NumSMin x
  NumSMax x        -> lift' NumSMax x
  NumSSize x       -> lift' NumSSize x
  NumSizeOf x      -> lift' NumSizeOf x  
  LtlNext x        -> lift' LtlNext x
  LtlGlobally x    -> lift' LtlGlobally x
  LtlFinally x     -> lift' LtlFinally x  
  NumPlus x y      -> lift2' NumPlus x y
  NumMinus x y     -> lift2' NumMinus x y
  NumMul x y       -> lift2' NumMul x y
  NumDiv x y       -> lift2' NumDiv x y
  NumMod x y       -> lift2' NumMod x y
  SetCup x y       -> lift2' SetCup x y
  SetCap x y       -> lift2' SetCap x y
  SetMinus x y     -> lift2' SetMinus x y
  BlnEQ x y        -> lift2' BlnEQ x y
  BlnNEQ x y       -> lift2' BlnNEQ x y
  BlnGE x y        -> lift2' BlnGE x y
  BlnGEQ x y       -> lift2' BlnGEQ x y
  BlnLE x y        -> lift2' BlnLE x y
  BlnLEQ x y       -> lift2' BlnLEQ x y
  BlnElem x y      -> lift2' BlnElem x y
  BlnOr x y        -> lift2' BlnOr x y
  BlnAnd x y       -> lift2' BlnAnd x y
  BlnImpl x y      -> lift2' BlnImpl x y
  BlnEquiv x y     -> lift2' BlnEquiv x y        
  LtlRNext x y     -> lift2' LtlRNext x y
  LtlRGlobally x y -> lift2' LtlRGlobally x y
  LtlRFinally x y  -> lift2' LtlRFinally x y
  LtlUntil x y     -> lift2' LtlUntil x y            
  LtlWeak x y      -> lift2' LtlWeak x y
  LtlRelease x y   -> lift2' LtlRelease x y  
  NumRPlus xs x    -> cond NumRPlus xs x 
  NumRMul xs x     -> cond NumRMul xs x 
  SetRCup xs x     -> cond SetRCup xs x 
  SetRCap xs x     -> cond SetRCap xs x 
  BlnROr xs x      -> cond BlnROr xs x 
  BlnRAnd xs x     -> cond BlnRAnd xs x 
  BaseId x         -> do
    (x',p) <- check (x,srcPos e)
    return $ Expr (BaseId x') p
  BaseBus x y      -> do
    (y',p) <- check (y,srcPos e)
    x' <- pcExpr x
    return $ Expr (BaseBus x' y') p
  BaseFml xs x     -> do
    (x',p) <- check (x,srcPos e)
    xs' <- mapM pcExpr xs
    return $ Expr (BaseFml xs' x') p
  SetExplicit xs   -> do
    xs' <- mapM pcExpr xs
    return $ Expr (SetExplicit xs') $ srcPos e
  SetRange x y z   -> do
    x' <- pcExpr x
    y' <- pcExpr y
    z' <- pcExpr z
    return $ Expr (SetRange x' y' z') $ srcPos e
  Colon v z        -> case expr v of
    Pattern x y -> do
      a <- get
      x' <- pcExpr x
      getPatternIds y 
      y' <- pcExpr y
      z' <- pcExpr z
      a' <- get
      put $ a' { tIndex = tIndex a }
      return $ Expr (Colon (Expr (Pattern x' y') (srcPos v)) z') (srcPos e)
    _ -> lift2' Colon v z 
  Pattern x y      -> lift2' Pattern x y

  where
    lift' c x = do
      x' <- pcExpr x
      return $ Expr (c x') (srcPos e)

    lift2' c x y = do
      x' <- pcExpr x
      y' <- pcExpr y      
      return $ Expr (c x' y') (srcPos e)
    
    cond c xs x = do
      a <- get
      _ <- mapM add $ mapMaybe getId xs
      xs' <- mapM pcExpr xs
      x' <- pcExpr x
      a' <- get
      put $ a' { tIndex = tIndex a }
      return $ Expr (c xs' x') (srcPos e)

    getId x = case expr x of
      BlnElem y _ -> isid y 
      BlnLE n _   -> range n 
      BlnLEQ n _  -> range n
      _          -> Nothing

    range n = case expr n of
      BlnLE _ m  -> isid m 
      BlnLEQ _ m -> isid m 
      _          -> Nothing
      
    isid m = case expr m of
      BaseId i -> Just (i,srcPos m)
      _        -> Nothing

    getPatternIds z = case expr z of
      BaseWild         -> return ()
      BaseTrue         -> return ()
      BaseFalse        -> return ()
      BaseOtherwise    -> return ()
      BaseId i         -> void $ add (i,srcPos z)      
      BlnNot x         -> getPatternIds x
      BlnOr x y        -> mapM_ getPatternIds [x,y]
      BlnAnd x y       -> mapM_ getPatternIds [x,y]
      BlnImpl x y      -> mapM_ getPatternIds [x,y]
      BlnEquiv x y     -> mapM_ getPatternIds [x,y]
      LtlNext x        -> getPatternIds x
      LtlRNext _ x     -> getPatternIds x
      LtlGlobally x    -> getPatternIds x
      LtlRGlobally _ x -> getPatternIds x
      LtlFinally x     -> getPatternIds x
      LtlRFinally _ x  -> getPatternIds x
      LtlUntil x y     -> mapM_ getPatternIds [x,y]
      LtlWeak x y      -> mapM_ getPatternIds [x,y]
      LtlRelease x y   -> mapM_ getPatternIds [x,y]      
      _                -> errPattern $ srcPos z

---