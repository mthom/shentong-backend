{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}

module Backend.Utils where

import Control.Monad.Except
import Control.Parallel
import qualified Data.Text as T
import Data.Monoid
import Core.Primitives
import Core.Types
import Core.Utils

applyWrapper :: KLValue -> [KLValue] -> KLContext Env KLValue
applyWrapper (ApplC ac) vs = ac `pseq` vs `pseq` foldr pseq (apply ac vs) vs
applyWrapper (Atom (UnboundSym fname)) vs = do
                ac <- fromIORef =<< functionRef fname
                ac `pseq` vs `pseq` foldr pseq (apply ac vs) vs
applyWrapper v _ = throwError $ "applyWrapper: expected fn in leading value, received" <> (T.pack $ show v)
