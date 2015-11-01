-----------------------------------------------------------------------------
-- |
-- Module      :  Config
-- License     :  MIT (see the LICENSE file)
-- Maintainer  :  Felix Klein (klein@react.uni-saarland.de)
-- 
-- Configuration of the tool, set up via the command line arguments.
-- 
-----------------------------------------------------------------------------

module Config
    ( Configuration(..)
    , parseArguments
    , defaultCfg  
    ) where

-----------------------------------------------------------------------------

import Data.Error
    ( Error
    , argsError
    )
    
import Writer.Formats
    ( WriteFormat(..)
    , parseFormat  
    )  

import Writer.Data
    ( WriteMode(..)
    )

-----------------------------------------------------------------------------

-- | The @Configuartion@ data type contains all flags and settings that can
-- be adjusted via the command line arguments. This includes:
-- 
--     * The list of input files containing the specifications
-- 
--     * An optional path to the output file, the transformed specification
--       is written to
-- 
--     * The format specifiying the corresponding writer to use
-- 
--     * The mode used by the writer
-- 
--     * A boolean flag specifying whether a partition file should be
--       createad or not
-- 
--     * A boolean flag specifying whether only a partition file should be
--       created or not
-- 
--     * The delimiter string to seperate the bus index from the signal
--       name
-- 
--     * A boolean flag specifying whether the input should be read from
--       STDIN or not
-- 
--     * An optional flag which allows to overwrite the semantics of the
--       given input specifications
-- 
--     * An optional flag which allows to overwrite the target of the
--       given input specifications
-- 
--     * An optional flag which allows to overwrite a list of parmaters
--       of the given input specification
-- 
--     * A boolean flag specifying whether weak simplifications should
--       be applied or not
-- 
--     * A boolean flag specifying whether strong simplifications should
--       be applied or not
-- 
--     * A boolean flag specifying whether the given specification should
--       be turned into negation normal form.
-- 
--     * A boolean flag specifying whether globally perators should be 
--       pushed over conjunctions deeper into the formula.
-- 
--     * A boolean flag specifying whether finally operators should be 
--       pushedover disjunctions deeper into the formula.
-- 
--     * A boolean flag specifying whether next operators should be pushed
--       over conjunctions and disjunctions deeper into the formula.
-- 
--     * A boolean flag specifying whether globally perators should be 
--       pulled over conjunctions outside the formula.
-- 
--     * A boolean flag specifying whether finally operators should be 
--       pulled over disjunctions outside the formula.
-- 
--     * A boolean flag specifying whether next operators should be pulled
--       over conjunctions and disjunctions outside the formula.
-- 
--     * A boolean flag specifying whether weak until operators should be
--       replaced by alternative operators inside the created formula.
-- 
--     * A boolean flag specifying whether release operators should be
--       replaced by alternative operators inside the created formula.
-- 
--     * A boolean flag specifying whether finally operators should be
--       replaced by alternative operators inside the created formula.
-- 
--     * A boolean flag specifying whether globally operators should be
--       replaced by alternative operators inside the created formula.
-- 
--     * A boolean flag specifying whether any derived operators should be
--       replaced by alternative operators inside the created formula.
-- 
--     * A boolean flag specifying whether the given input files should
--       just be checked for syntactical and type correctenss.
-- 
--     * A boolean flag specifying whether just the title of the given
--       input files should be printed or not
-- 
--     * A boolean flag specifying whether just the description of the
--       given input files should be printed or not
-- 
--     * A boolean flag specifying whether just the semantics of the 
--       given input files should be printed or not
-- 
--     * A boolean flag specifying whether just the target of the given
--       input files should be printed or not
-- 
--     * A boolean flag specifying whether just the tag list  of the 
--       given input files should be printed or not
-- 
--     * A boolean flag specifying whether just the complete input section 
--        of the given input files should be printed or not
-- 
--     * A boolean flag specifying whether the version info should be
--       printed or not
-- 
--     * A boolean flag specifying whether the help info should be
--       printed or not

data Configuration =
  Configuration
  { inputFile :: [String]
  , outputFile :: Maybe String
  , outputFormat :: WriteFormat
  , outputMode :: WriteMode
  , noPartition :: Bool
  , onlyPartition :: Bool
  , busDelimiter :: String
  , fromStdin :: Bool
  , owSemantics :: Maybe String
  , owTarget :: Maybe String
  , owParameter :: [String]
  , simplifyWeak :: Bool
  , simplifyStrong :: Bool
  , negNormalForm :: Bool
  , pushGlobally :: Bool
  , pushFinally :: Bool
  , pushNext :: Bool
  , pullGlobally :: Bool
  , pullFinally :: Bool
  , pullNext :: Bool
  , noWeak :: Bool
  , noRelease :: Bool
  , noFinally :: Bool
  , noGlobally :: Bool
  , noDerived :: Bool
  , check :: Bool
  , pTitle :: Bool
  , pDesc :: Bool
  , pSemantics :: Bool
  , pTarget :: Bool
  , pTags :: Bool    
  , pParameters :: Bool
  , pInfo :: Bool
  , pVersion :: Bool  
  , pHelp :: Bool
  }

-----------------------------------------------------------------------------

-- | The default configuration.

defaultCfg
  :: Configuration

defaultCfg =
  Configuration {
    inputFile = [],
    outputFile = Nothing,
    outputFormat = UTF8,
    outputMode = Pretty,
    noPartition = False,
    onlyPartition = False,
    busDelimiter = "\"_\"",
    fromStdin = False,
    owSemantics = Nothing,
    owTarget = Nothing,
    owParameter = [],
    simplifyWeak = False,
    simplifyStrong = False,
    negNormalForm = False,
    pushGlobally = False,
    pushFinally = False,
    pushNext = False,
    pullGlobally = False,
    pullFinally = False,
    pullNext = False,
    noWeak = False,
    noRelease = False,
    noFinally = False,
    noGlobally = False,
    noDerived = False,
    check = False,
    pTitle = False,
    pDesc = False,
    pSemantics = False,
    pTarget = False,
    pTags = False,
    pParameters = False,
    pInfo = False,
    pVersion = False,
    pHelp = False
    }

-----------------------------------------------------------------------------

data Args a = None a | Single a

-----------------------------------------------------------------------------

-- | Argument parser, which reads the given command line arguments to
-- the internal configuration and checks whether the given combinations
-- are realizable.

parseArguments
  :: [String] -> Either Error Configuration

parseArguments args = do
  c <- traverse parseArgument defaultCfg args
  checkConfiguration c
  return c { busDelimiter = fixquotes $ busDelimiter c }
  
  where
    traverse f a xs = case xs of
      x:y:xr -> case f a x (Just y) of
        Right (Single z) -> traverse f z xr
        Right (None z)   -> traverse f z (y:xr)
        Left err         -> Left err        
      [x]    -> case f a x Nothing of
        Right (None z)   -> return z
        Right (Single z) -> return z
        Left err         -> Left err        
      []     -> return a

    parseArgument a arg next = case arg of
      "-o"                       -> case next of
        Just x  -> return $ Single $ a { outputFile = Just x }
        Nothing -> argsError "\"-o\": No output file"
      "--output"                 -> case next of
        Nothing -> argsError "\"--output\": No output file"
        _       -> parseArgument a "-o" next
      "-f"                       -> case next of
        Just x  -> do
          y <- parseFormat x
          return $ Single $ a { outputFormat = y }
        Nothing ->
          argsError "\"-f\": No format given"
      "--format"                 -> case next of
        Nothing -> argsError "\"--format\": No format given"
        _       -> parseArgument a "-f" next
      "-m"                       -> case next of
        Just "pretty" -> return $ Single $ a { outputMode = Pretty }
        Just "fully"  -> return $ Single $ a { outputMode = Fully }
        Just x        -> argsError ("Unknown mode: " ++ x)
        Nothing       -> argsError "\"-m\": No mode given"
      "--mode"                   -> case next of
        Nothing -> argsError "\"--mode\": no mode given"
        _       -> parseArgument a "-m" next        
      "-np"                      -> return $ None $ a { noPartition = True }
      "-po"                      -> return $ None $ a { onlyPartition = True }
      "-bd"                      -> case next of
        Just x  -> return $ Single $ a { busDelimiter = x }
        Nothing -> argsError "\"-bd\": No delimiter given"
      "--bus-delimiter"          -> case next of
        Nothing -> argsError "\"--bus-delimiter\": No delimiter given"
        _       ->parseArgument a "-bd" next        
      "-in"                      -> return $ None $ a { fromStdin = True }
      "-os"                      -> case next of
        Just x  -> return $ Single $ a { owSemantics = Just x }
        Nothing -> argsError "\"-os\": No semantics given"
      "--overwrite-semantics"    -> case next of
        Nothing -> argsError "\"--overwrite-semantics\": No semantics given"
        _       -> parseArgument a "-os" next        
      "-ot"                      -> case next of
        Just x  -> return $ Single $ a { owTarget = Just x }
        Nothing -> argsError "\"-ot\": No target given"
      "--overwrite-target"       -> case next of
        Nothing -> argsError "\"--overwrite-target\": No target given"
        _       -> parseArgument a "-ot" next        
      "-op"                      -> case next of
        Just x  -> return $ Single $ a { owParameter = x : owParameter a }
        Nothing -> argsError "\"-op\": No parameter given"
      "--overwrite-parameter"    -> case next of
        Nothing -> argsError "\"--overwrite-parameter\": No parameter given"
        _       -> parseArgument a "-op" next        
      "-s0"                      -> simple $ a { simplifyWeak = True }
      "-s1"                      -> simple $ a { simplifyStrong = True }
      "-nnf"                     -> simple $ a { negNormalForm = True }
      "-pgi"                     -> simple $ a { pushGlobally = True }
      "-pfi"                     -> simple $ a { pushFinally = True }
      "-pxi"                     -> simple $ a { pushNext = True }
      "-pgo"                     -> simple $ a { pullGlobally = True }
      "-pfo"                     -> simple $ a { pullFinally = True }
      "-pxo"                     -> simple $ a { pullNext = True }
      "-nw"                      -> simple $ a { noWeak = True }
      "-nr"                      -> simple $ a { noRelease = True }
      "-nf"                      -> simple $ a { noFinally = True }
      "-ng"                      -> simple $ a { noGlobally = True }
      "-nd"                      -> simple $ a { noDerived = True }
      "-c"                       -> simple $ (clean a) { check = True }
      "-t"                       -> simple $ (clean a) { pTitle = True }
      "-d"                       -> simple $ (clean a) { pDesc = True }
      "-s"                       -> simple $ (clean a) { pSemantics = True }
      "-g"                       -> simple $ (clean a) { pTarget = True }
      "-a"                       -> simple $ (clean a) { pTags = True }      
      "-p"                       -> simple $ (clean a) { pParameters = True }
      "-i"                       -> simple $ (clean a) { pInfo = True }
      "-v"                       -> simple $ (clean a) { pVersion = True }
      "-h"                       -> simple $ (clean a) { pHelp = True }
      "--no-part"                -> parseArgument a "-np" next
      "--part-only"              -> parseArgument a "-po" next
      "--stdin"                  -> parseArgument a "-in" next
      "--weak-simplify"          -> parseArgument a "-s0" next
      "--strong-simplify"        -> parseArgument a "-s1" next
      "--negation-normal-form"   -> parseArgument a "-nnf" next
      "--push-globally-inwards"  -> parseArgument a "-pgi" next
      "--push-finally-inwards"   -> parseArgument a "-pfi" next
      "--push-next-inwards"      -> parseArgument a "-pni" next
      "--pull-globally-outwards" -> parseArgument a "-pgo" next
      "--pull-finally-outwards"  -> parseArgument a "-pfo" next
      "--pull-next-outwards"     -> parseArgument a "-pxo" next
      "--no-weak-until"          -> parseArgument a "-nw" next
      "--no-realease"            -> parseArgument a "-nr" next
      "--no-finally"             -> parseArgument a "-nf" next
      "--no-globally"            -> parseArgument a "-ng" next
      "--no-derived"             -> parseArgument a "-nd" next
      "--check"                  -> parseArgument a "-c" next
      "--print-title"            -> parseArgument a "-t" next
      "--print-description"      -> parseArgument a "-d" next
      "--print-semantics"        -> parseArgument a "-s" next
      "--print-target"           -> parseArgument a "-g" next
      "--print-tags"             -> parseArgument a "-a" next      
      "--print-parameters"       -> parseArgument a "-p" next
      "--print-info"             -> parseArgument a "-i" next
      "--version"                -> parseArgument a "-v" next
      "--help"                   -> parseArgument a "-h" next      
      _                          -> return $ None $ a {
                                     inputFile = arg : inputFile a
                                     }

    clean a = a {
      check = False,
      pTitle = False,
      pDesc = False,
      pSemantics = False,
      pTarget = False,
      pParameters = False,
      pInfo = False,
      pVersion = False,
      pHelp = False
      }

    fixquotes s = tail $ init s

    simple = return . None

-----------------------------------------------------------------------------

checkConfiguration
  :: Configuration -> Either Error ()

checkConfiguration cfg
  | pHelp cfg || pVersion cfg =

      return ()
    
  | null (inputFile cfg) && not(fromStdin cfg) =

      argsError
        "no input specified"
        
  | not (null (inputFile cfg)) && fromStdin cfg =

      argsError
        "Select either \"-in, --stdin\" or give an input file."
        
  | noPartition cfg && onlyPartition cfg =
    
      argsError
        "Select either \"-np, --no-part\" or \"-po, --part-only\"."
        
  | pushGlobally cfg && pullGlobally cfg =

      argsError $
        "Select either \"-pgi, --push-globally-inwards\" or " ++
        "\"-pgo, --pull-globally-outwards\"."
        
  | pushFinally cfg && pullFinally cfg =

      argsError $
        "Select either \"-pfi, --push-finally-inwards\" or " ++
        "\"-pfo, --pull-finally-outwards\"."
        
  | pushNext cfg && pullNext cfg =

      argsError $
        "Select either \"-pxi, --push-next-inwards\" or " ++
        "\"-pxo, --pull-next-outwards\"."
        
  | simplifyStrong cfg && (pushGlobally cfg || pushFinally cfg ||
                           pushNext cfg || noFinally cfg ||
                           noGlobally cfg || noDerived cfg) =
    
      argsError $
        "The flag 'Advanced Simplifications' cannot be combined " ++
        "with any other non-included transformation."
        
  | missingQuotes (busDelimiter cfg) =

      argsError $
        "The argument of \"-bd, --bus-delimiter\" has " ++
        "to be sourrounded by double quotes."
        
  | negNormalForm cfg && noRelease cfg && noGlobally cfg && noWeak cfg =

      argsError $
        "The given combination of transformations " ++
        "(negation normal form, no release operators, " ++
        "no globally operators, and no weak until operatators)" ++
        "is impossible to satisfy.\n" ++
        "Remove at least one of these constaints."
      
  | negNormalForm cfg && noRelease cfg && noDerived cfg =
        
      argsError $
        "The given combination of transformations " ++
        "(negation normal form, no release operatators, " ++
        "and no derived operators) is impossible to satisfy.\n" ++
        "Remove at least one of these constraints."
        
  | otherwise = return ()

  where
    missingQuotes str =
      length str < 2 ||
      head str /= '"' ||
      last str /= '"'

-----------------------------------------------------------------------------
