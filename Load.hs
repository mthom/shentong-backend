{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Backend.Load where

import Control.Monad.Except
import Control.Parallel
import Environment
import Core.Primitives as Primitives
import Backend.Utils
import Core.Types
import Core.Utils
import Wrap
import Backend.Toplevel
import Backend.Core
import Backend.Sys
import Backend.Sequent
import Backend.Yacc
import Backend.Reader
import Backend.Prolog
import Backend.Track

{-
Copyright (c) 2015, Mark Tarver
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. The name of Mark Tarver may not be used to endorse or promote products
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-}

kl_load :: Core.Types.KLValue ->
           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_load (!kl_V1482) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Load) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Infs) -> do return (Core.Types.Atom (Core.Types.UnboundSym "loaded")))))
                                                                                        !kl_if_2 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*tc*"))
                                                                                        !appl_3 <- case kl_if_2 of
                                                                                                       Atom (B (True)) -> do !appl_4 <- kl_inferences
                                                                                                                             let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                             !appl_6 <- appl_4 `pseq` applyWrapper aw_5 [appl_4,
                                                                                                                                                                         Core.Types.Atom (Core.Types.Str " inferences\n"),
                                                                                                                                                                         Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                                                                                             !appl_7 <- appl_6 `pseq` cn (Core.Types.Atom (Core.Types.Str "\ntypechecked in ")) appl_6
                                                                                                                             !appl_8 <- kl_stoutput
                                                                                                                             let !aw_9 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                                                                             appl_7 `pseq` (appl_8 `pseq` applyWrapper aw_9 [appl_7,
                                                                                                                                                                             appl_8])
                                                                                                       Atom (B (False)) -> do do return (Core.Types.Atom (Core.Types.UnboundSym "shen.skip"))
                                                                                                       _ -> throwError "if: expected boolean"
                                                                                        appl_3 `pseq` applyWrapper appl_1 [appl_3])))
                         let !appl_10 = ApplC (Func "lambda" (Context (\(!kl_Start) -> do let !appl_11 = ApplC (Func "lambda" (Context (\(!kl_Result) -> do let !appl_12 = ApplC (Func "lambda" (Context (\(!kl_Finish) -> do let !appl_13 = ApplC (Func "lambda" (Context (\(!kl_Time) -> do let !appl_14 = ApplC (Func "lambda" (Context (\(!kl_Message) -> do return kl_Result)))
                                                                                                                                                                                                                                                                                              !appl_15 <- kl_Time `pseq` str kl_Time
                                                                                                                                                                                                                                                                                              !appl_16 <- appl_15 `pseq` cn appl_15 (Core.Types.Atom (Core.Types.Str " secs\n"))
                                                                                                                                                                                                                                                                                              !appl_17 <- appl_16 `pseq` cn (Core.Types.Atom (Core.Types.Str "\nrun time: ")) appl_16
                                                                                                                                                                                                                                                                                              !appl_18 <- kl_stoutput
                                                                                                                                                                                                                                                                                              let !aw_19 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                                                                                                                                                                                                                                              !appl_20 <- appl_17 `pseq` (appl_18 `pseq` applyWrapper aw_19 [appl_17,
                                                                                                                                                                                                                                                                                                                                                             appl_18])
                                                                                                                                                                                                                                                                                              appl_20 `pseq` applyWrapper appl_14 [appl_20])))
                                                                                                                                                                                                                              !appl_21 <- kl_Finish `pseq` (kl_Start `pseq` Primitives.subtract kl_Finish kl_Start)
                                                                                                                                                                                                                              appl_21 `pseq` applyWrapper appl_13 [appl_21])))
                                                                                                                                                            !appl_22 <- getTime (Core.Types.Atom (Core.Types.UnboundSym "run"))
                                                                                                                                                            appl_22 `pseq` applyWrapper appl_12 [appl_22])))
                                                                                          !appl_23 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*tc*"))
                                                                                          !appl_24 <- kl_V1482 `pseq` kl_read_file kl_V1482
                                                                                          !appl_25 <- appl_23 `pseq` (appl_24 `pseq` kl_shen_load_help appl_23 appl_24)
                                                                                          appl_25 `pseq` applyWrapper appl_11 [appl_25])))
                         !appl_26 <- getTime (Core.Types.Atom (Core.Types.UnboundSym "run"))
                         !appl_27 <- appl_26 `pseq` applyWrapper appl_10 [appl_26]
                         appl_27 `pseq` applyWrapper appl_0 [appl_27]

kl_shen_load_help :: Core.Types.KLValue ->
                     Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_load_help (!kl_V1489) (!kl_V1490) = do let pat_cond_0 = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_X) -> do !appl_2 <- kl_X `pseq` kl_shen_eval_without_macros kl_X
                                                                                                                               let !aw_3 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                               !appl_4 <- appl_2 `pseq` applyWrapper aw_3 [appl_2,
                                                                                                                                                                           Core.Types.Atom (Core.Types.Str "\n"),
                                                                                                                                                                           Core.Types.Atom (Core.Types.UnboundSym "shen.s")]
                                                                                                                               !appl_5 <- kl_stoutput
                                                                                                                               let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                                                                               appl_4 `pseq` (appl_5 `pseq` applyWrapper aw_6 [appl_4,
                                                                                                                                                                               appl_5]))))
                                                                   appl_1 `pseq` (kl_V1490 `pseq` kl_for_each appl_1 kl_V1490)
                                                   pat_cond_7 = do do let !appl_8 = ApplC (Func "lambda" (Context (\(!kl_RemoveSynonyms) -> do let !appl_9 = ApplC (Func "lambda" (Context (\(!kl_Table) -> do let !appl_10 = ApplC (Func "lambda" (Context (\(!kl_Assume) -> do (do let !appl_11 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_typecheck_and_load kl_X)))
                                                                                                                                                                                                                                                                                     appl_11 `pseq` (kl_RemoveSynonyms `pseq` kl_for_each appl_11 kl_RemoveSynonyms)) `catchError` (\(!kl_E) -> do kl_E `pseq` (kl_Table `pseq` kl_shen_unwind_types (Excep kl_E) kl_Table)))))
                                                                                                                                                                                                               let !appl_12 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_assumetype kl_X)))
                                                                                                                                                                                                               !appl_13 <- appl_12 `pseq` (kl_Table `pseq` kl_for_each appl_12 kl_Table)
                                                                                                                                                                                                               appl_13 `pseq` applyWrapper appl_10 [appl_13])))
                                                                                                                                               let !appl_14 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_typetable kl_X)))
                                                                                                                                               !appl_15 <- appl_14 `pseq` (kl_RemoveSynonyms `pseq` kl_mapcan appl_14 kl_RemoveSynonyms)
                                                                                                                                               appl_15 `pseq` applyWrapper appl_9 [appl_15])))
                                                                      let !appl_16 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_remove_synonyms kl_X)))
                                                                      !appl_17 <- appl_16 `pseq` (kl_V1490 `pseq` kl_mapcan appl_16 kl_V1490)
                                                                      appl_17 `pseq` applyWrapper appl_8 [appl_17]
                                                in case kl_V1489 of
                                                       kl_V1489@(Atom (UnboundSym "false")) -> pat_cond_0
                                                       kl_V1489@(Atom (B (False))) -> pat_cond_0
                                                       _ -> pat_cond_7

kl_shen_remove_synonyms :: Core.Types.KLValue ->
                           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_remove_synonyms (!kl_V1492) = do let pat_cond_0 kl_V1492 kl_V1492t = do !appl_1 <- kl_V1492 `pseq` kl_eval kl_V1492
                                                                                let !appl_2 = Atom Nil
                                                                                appl_1 `pseq` (appl_2 `pseq` kl_do appl_1 appl_2)
                                             pat_cond_3 = do do let !appl_4 = Atom Nil
                                                                kl_V1492 `pseq` (appl_4 `pseq` klCons kl_V1492 appl_4)
                                          in case kl_V1492 of
                                                 !(kl_V1492@(Cons (Atom (UnboundSym "shen.synonyms-help"))
                                                                  (!kl_V1492t))) -> pat_cond_0 kl_V1492 kl_V1492t
                                                 !(kl_V1492@(Cons (ApplC (PL "shen.synonyms-help"
                                                                             _))
                                                                  (!kl_V1492t))) -> pat_cond_0 kl_V1492 kl_V1492t
                                                 !(kl_V1492@(Cons (ApplC (Func "shen.synonyms-help"
                                                                               _))
                                                                  (!kl_V1492t))) -> pat_cond_0 kl_V1492 kl_V1492t
                                                 _ -> pat_cond_3

kl_shen_typecheck_and_load :: Core.Types.KLValue ->
                              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_typecheck_and_load (!kl_V1494) = do !appl_0 <- kl_nl (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                            !appl_1 <- kl_gensym (Core.Types.Atom (Core.Types.UnboundSym "A"))
                                            !appl_2 <- kl_V1494 `pseq` (appl_1 `pseq` kl_shen_typecheck_and_evaluate kl_V1494 appl_1)
                                            appl_0 `pseq` (appl_2 `pseq` kl_do appl_0 appl_2)

kl_shen_typetable :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_typetable (!kl_V1500) = do let pat_cond_0 kl_V1500 kl_V1500t kl_V1500th kl_V1500tt = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Sig) -> do !appl_2 <- kl_V1500th `pseq` (kl_Sig `pseq` klCons kl_V1500th kl_Sig)
                                                                                                                                                              let !appl_3 = Atom Nil
                                                                                                                                                              appl_2 `pseq` (appl_3 `pseq` klCons appl_2 appl_3))))
                                                                                                let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do kl_Y `pseq` kl_shen_LBsigPlusrestRB kl_Y)))
                                                                                                let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_E) -> do let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                                                            !appl_7 <- kl_V1500th `pseq` applyWrapper aw_6 [kl_V1500th,
                                                                                                                                                                                                            Core.Types.Atom (Core.Types.Str " lacks a proper signature.\n"),
                                                                                                                                                                                                            Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                                                                                                                            appl_7 `pseq` simpleError appl_7)))
                                                                                                !appl_8 <- appl_4 `pseq` (kl_V1500tt `pseq` (appl_5 `pseq` kl_compile appl_4 kl_V1500tt appl_5))
                                                                                                appl_8 `pseq` applyWrapper appl_1 [appl_8]
                                       pat_cond_9 = do do return (Atom Nil)
                                    in case kl_V1500 of
                                           !(kl_V1500@(Cons (Atom (UnboundSym "define"))
                                                            (!(kl_V1500t@(Cons (!kl_V1500th)
                                                                               (!kl_V1500tt)))))) -> pat_cond_0 kl_V1500 kl_V1500t kl_V1500th kl_V1500tt
                                           !(kl_V1500@(Cons (ApplC (PL "define" _))
                                                            (!(kl_V1500t@(Cons (!kl_V1500th)
                                                                               (!kl_V1500tt)))))) -> pat_cond_0 kl_V1500 kl_V1500t kl_V1500th kl_V1500tt
                                           !(kl_V1500@(Cons (ApplC (Func "define" _))
                                                            (!(kl_V1500t@(Cons (!kl_V1500th)
                                                                               (!kl_V1500tt)))))) -> pat_cond_0 kl_V1500 kl_V1500t kl_V1500th kl_V1500tt
                                           _ -> pat_cond_9

kl_shen_assumetype :: Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_assumetype (!kl_V1502) = do let pat_cond_0 kl_V1502 kl_V1502h kl_V1502t = do let !aw_1 = Core.Types.Atom (Core.Types.UnboundSym "declare")
                                                                                     kl_V1502h `pseq` (kl_V1502t `pseq` applyWrapper aw_1 [kl_V1502h,
                                                                                                                                           kl_V1502t])
                                        pat_cond_2 = do do kl_shen_f_error (ApplC (wrapNamed "shen.assumetype" kl_shen_assumetype))
                                     in case kl_V1502 of
                                            !(kl_V1502@(Cons (!kl_V1502h)
                                                             (!kl_V1502t))) -> pat_cond_0 kl_V1502 kl_V1502h kl_V1502t
                                            _ -> pat_cond_2

kl_shen_unwind_types :: Core.Types.KLValue ->
                        Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_unwind_types (!kl_V1509) (!kl_V1510) = do let !appl_0 = Atom Nil
                                                  !kl_if_1 <- appl_0 `pseq` (kl_V1510 `pseq` eq appl_0 kl_V1510)
                                                  case kl_if_1 of
                                                      Atom (B (True)) -> do !appl_2 <- kl_V1509 `pseq` errorToString kl_V1509
                                                                            appl_2 `pseq` simpleError appl_2
                                                      Atom (B (False)) -> do let pat_cond_3 kl_V1510 kl_V1510h kl_V1510hh kl_V1510ht kl_V1510t = do !appl_4 <- kl_V1510hh `pseq` kl_shen_remtype kl_V1510hh
                                                                                                                                                    !appl_5 <- kl_V1509 `pseq` (kl_V1510t `pseq` kl_shen_unwind_types kl_V1509 kl_V1510t)
                                                                                                                                                    appl_4 `pseq` (appl_5 `pseq` kl_do appl_4 appl_5)
                                                                                 pat_cond_6 = do do kl_shen_f_error (ApplC (wrapNamed "shen.unwind-types" kl_shen_unwind_types))
                                                                              in case kl_V1510 of
                                                                                     !(kl_V1510@(Cons (!(kl_V1510h@(Cons (!kl_V1510hh)
                                                                                                                         (!kl_V1510ht))))
                                                                                                      (!kl_V1510t))) -> pat_cond_3 kl_V1510 kl_V1510h kl_V1510hh kl_V1510ht kl_V1510t
                                                                                     _ -> pat_cond_6
                                                      _ -> throwError "if: expected boolean"

kl_shen_remtype :: Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_remtype (!kl_V1512) = do !appl_0 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*signedfuncs*"))
                                 !appl_1 <- kl_V1512 `pseq` (appl_0 `pseq` kl_shen_removetype kl_V1512 appl_0)
                                 appl_1 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*signedfuncs*")) appl_1

kl_shen_removetype :: Core.Types.KLValue ->
                      Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_removetype (!kl_V1520) (!kl_V1521) = do let !appl_0 = Atom Nil
                                                !kl_if_1 <- appl_0 `pseq` (kl_V1521 `pseq` eq appl_0 kl_V1521)
                                                case kl_if_1 of
                                                    Atom (B (True)) -> do return (Atom Nil)
                                                    Atom (B (False)) -> do let pat_cond_2 kl_V1521 kl_V1521h kl_V1521hh kl_V1521ht kl_V1521t = do kl_V1521hh `pseq` (kl_V1521t `pseq` kl_shen_removetype kl_V1521hh kl_V1521t)
                                                                               pat_cond_3 kl_V1521 kl_V1521h kl_V1521t = do !appl_4 <- kl_V1520 `pseq` (kl_V1521t `pseq` kl_shen_removetype kl_V1520 kl_V1521t)
                                                                                                                            kl_V1521h `pseq` (appl_4 `pseq` klCons kl_V1521h appl_4)
                                                                               pat_cond_5 = do do kl_shen_f_error (ApplC (wrapNamed "shen.removetype" kl_shen_removetype))
                                                                            in case kl_V1521 of
                                                                                   !(kl_V1521@(Cons (!(kl_V1521h@(Cons (!kl_V1521hh)
                                                                                                                       (!kl_V1521ht))))
                                                                                                    (!kl_V1521t))) | eqCore kl_V1521hh kl_V1520 -> pat_cond_2 kl_V1521 kl_V1521h kl_V1521hh kl_V1521ht kl_V1521t
                                                                                   !(kl_V1521@(Cons (!kl_V1521h)
                                                                                                    (!kl_V1521t))) -> pat_cond_3 kl_V1521 kl_V1521h kl_V1521t
                                                                                   _ -> pat_cond_5
                                                    _ -> throwError "if: expected boolean"

kl_shen_LBsigPlusrestRB :: Core.Types.KLValue ->
                           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_LBsigPlusrestRB (!kl_V1523) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Parse_shen_LBsignatureRB) -> do !appl_1 <- kl_fail
                                                                                                                            !appl_2 <- appl_1 `pseq` (kl_Parse_shen_LBsignatureRB `pseq` eq appl_1 kl_Parse_shen_LBsignatureRB)
                                                                                                                            !kl_if_3 <- appl_2 `pseq` kl_not appl_2
                                                                                                                            case kl_if_3 of
                                                                                                                                Atom (B (True)) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Parse_LBExclRB) -> do !appl_5 <- kl_fail
                                                                                                                                                                                                                               !appl_6 <- appl_5 `pseq` (kl_Parse_LBExclRB `pseq` eq appl_5 kl_Parse_LBExclRB)
                                                                                                                                                                                                                               !kl_if_7 <- appl_6 `pseq` kl_not appl_6
                                                                                                                                                                                                                               case kl_if_7 of
                                                                                                                                                                                                                                   Atom (B (True)) -> do !appl_8 <- kl_Parse_LBExclRB `pseq` hd kl_Parse_LBExclRB
                                                                                                                                                                                                                                                         !appl_9 <- kl_Parse_shen_LBsignatureRB `pseq` kl_shen_hdtl kl_Parse_shen_LBsignatureRB
                                                                                                                                                                                                                                                         appl_8 `pseq` (appl_9 `pseq` kl_shen_pair appl_8 appl_9)
                                                                                                                                                                                                                                   Atom (B (False)) -> do do kl_fail
                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean")))
                                                                                                                                                      !appl_10 <- kl_Parse_shen_LBsignatureRB `pseq` kl_LBExclRB kl_Parse_shen_LBsignatureRB
                                                                                                                                                      appl_10 `pseq` applyWrapper appl_4 [appl_10]
                                                                                                                                Atom (B (False)) -> do do kl_fail
                                                                                                                                _ -> throwError "if: expected boolean")))
                                         !appl_11 <- kl_V1523 `pseq` kl_shen_LBsignatureRB kl_V1523
                                         appl_11 `pseq` applyWrapper appl_0 [appl_11]

kl_write_to_file :: Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_write_to_file (!kl_V1526) (!kl_V1527) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Stream) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_String) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Write) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Close) -> do return kl_V1527)))
                                                                                                                                                                                                                                                !appl_4 <- kl_Stream `pseq` closeStream kl_Stream
                                                                                                                                                                                                                                                appl_4 `pseq` applyWrapper appl_3 [appl_4])))
                                                                                                                                                                                let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "pr")
                                                                                                                                                                                !appl_6 <- kl_String `pseq` (kl_Stream `pseq` applyWrapper aw_5 [kl_String,
                                                                                                                                                                                                                                                 kl_Stream])
                                                                                                                                                                                appl_6 `pseq` applyWrapper appl_2 [appl_6])))
                                                                                                               !kl_if_7 <- kl_V1527 `pseq` stringP kl_V1527
                                                                                                               !appl_8 <- case kl_if_7 of
                                                                                                                              Atom (B (True)) -> do let !aw_9 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                                                    kl_V1527 `pseq` applyWrapper aw_9 [kl_V1527,
                                                                                                                                                                                       Core.Types.Atom (Core.Types.Str "\n\n"),
                                                                                                                                                                                       Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                                                                                              Atom (B (False)) -> do do let !aw_10 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                                                        kl_V1527 `pseq` applyWrapper aw_10 [kl_V1527,
                                                                                                                                                                                            Core.Types.Atom (Core.Types.Str "\n\n"),
                                                                                                                                                                                            Core.Types.Atom (Core.Types.UnboundSym "shen.s")]
                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                               appl_8 `pseq` applyWrapper appl_1 [appl_8])))
                                              !appl_11 <- kl_V1526 `pseq` openStream kl_V1526 (Core.Types.Atom (Core.Types.UnboundSym "out"))
                                              appl_11 `pseq` applyWrapper appl_0 [appl_11]

expr8 :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
expr8 = do (do return (Core.Types.Atom (Core.Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
