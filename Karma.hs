module KarmaBrief where

import System.Random
import Control.Monad.State
import Data.List
import Data.Ord
import Data.Function
import Test.HUnit (Testable(test))
import Foreign (new)
import GHC.Read (choose)


-- Cards
data Suit = Clubs | Diamonds | Hearts | Spades
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

data Rank = R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | RJ | RQ | RK | RA
  deriving (Eq, Enum, Bounded, Read)

--for displaying to user
instance Show Rank where
  show R2  = "2"
  show R3  = "3"
  show R4  = "4"
  show R5  = "5"
  show R6  = "6"
  show R7  = "7"
  show R8  = "8"
  show R9  = "9"
  show R10 = "10"
  show RJ  = "Jack"
  show RQ  = "Queen"
  show RK  = "King"
  show RA  = "Ace"

instance Ord Rank where--8 and 10 should never be passed in as a top card so 2 can always be played
  compare R10 R10 = EQ
  compare R10 _  = GT
  compare _ R10  = LT
  compare R8 R8 = EQ
  compare R8 _  = GT
  compare _ R8  = LT
  compare R2 R2 = EQ
  compare R2 _  = GT
  compare _ R2  = LT
  compare r1 r2 = compare (fromEnum r1) (fromEnum r2)


data Card = Card { rank :: Rank, suit :: Suit }
  deriving (Eq, Read)

--shows information about card neatly
instance Show Card where
  show (Card r s) = show r ++ " of " ++ show s

type Deck = [Card]
type Pile = [Card]

-- Players
type PlayerId   = Int
type PlayerName = String

data Player = Player
  { pId       :: PlayerId
  , pName     :: PlayerName
  , hand      :: [Card]
  , faceUp    :: [Card]
  , faceDown  :: [Card]
  , strategy  :: (State GameState Deck)
  }

-- Game state 
data GameState = GameState
  { players       :: [Player]    -- clockwise order
  , currentIx     :: Int         -- index into players
  , drawPile      :: Deck
  , discardPile   :: Pile
  , burnedPiles   :: [Pile]
  , rng           :: StdGen      -- random number generator
  , finishedOrder :: [PlayerId]
  , roundNum      :: Int         -- number of rounds that have been played
  , inc           :: Bool        -- records direction of play
  }


-- Different extension rules
data Extension = ExtReverse8 | ExtThree3s | ExtNineClubs
  deriving (Eq, Show)


legalPlay :: Maybe Card -> Card -> Bool
legalPlay Nothing _ = True
legalPlay (Just topCard) c
  | rank c == R2 || rank c == R8 || rank c == R10 = True -- 2 10 and 8 can always be played
  | rank topCard == R7 = rank c <= R7 -- must play 7 or lower on 7
  | rank topCard == R2 = True -- any card can be played on 2
  | otherwise = rank topCard <= rank c -- otherwise must be equal or higher 
                                       

maybeTopCard :: Deck -> Maybe Card
maybeTopCard [] = Nothing
maybeTopCard xs = if rank (head xs) == R8 then
                    maybeTopCard (tail xs) -- if 8 inspect the next card
                  else
                    Just (head xs) -- return top card as maybe

validPlays :: Maybe Card -> Deck -> Deck--filters deck for cards that are legal to play
validPlays mCard deck = [card |card <- deck, legalPlay mCard card]

dealCards :: Int -> State GameState Deck
dealCards num = do
  gs <- get
  put gs {drawPile = drop num (drawPile gs)}--removes cards from draw pile
  return (take num (drawPile gs))--returns cards

giveWastePileTo :: Player -> State GameState ()
giveWastePileTo player = do
  gs <- get
  --give discard pile to player
  let newps = replacePlayer gs (player{hand = hand player ++ discardPile gs})
  put gs{players = newps, discardPile = []}--clears discard pile
  return ()


replenishCards :: Player -> State GameState ()
replenishCards player = do
  if length (hand player) < 3 then do--check if player has less than 3 cards
    gs <- get
    let num = 3 - length (hand player)--number of cards to replenish
        --list containing replenished player
        newps = replacePlayer gs player{hand = hand player ++ evalState (dealCards num) gs}
    put (execState (dealCards num) gs){players = newps}--removes cards from draw pile
    return ()
  else do
    return ()


shuffleDeck :: StdGen -> Deck -> Deck--sorts deck based on random indexes
shuffleDeck gen deck= [card | (card, _) <- shuffledDeck :: [(Card, Int)]]
  where 
    randomNumbers = randoms gen--generates random indexes
    shuffledDeck = sortBy (compare `on` snd) (zip deck randomNumbers)




replacePlayer :: GameState -> Player -> [Player]--replace player with matching id in the GameState
replacePlayer gs player = [if pId p == pId player then player else p| p <- ps]
  where ps = players gs



basicStrategy :: State GameState Deck
basicStrategy = do
  gs <- get
  let player = players gs !! currentIx gs
      topCard = maybeTopCard (discardPile gs)
  --if there are cards in hand
  if (not.null) (hand player) then do
    let card = sMinimum (validPlays topCard (hand player))
    put gs{players = replacePlayer gs (player{hand = sRemove (hand player) card})}
    return card
  --no card in hand but cards in faceUp
  else if null (drawPile gs) && (not.null) (faceUp player) then do
    let card = playFaceUp player topCard
    put gs{players = replacePlayer gs (player{faceUp = sRemove (faceUp player) card})}
    return card
  --no cards in hand or faceUp but faceDown
  else if null (drawPile gs) && null (faceUp player) then do
    let card = [head (faceDown player)]
    put gs{players = replacePlayer gs (player{faceDown = tail (faceDown player)})}
    return card
  --this is only here for safety if it runs player should have already been out
  else do
    put gs
    return []
  where
    --when playing faceUp cards a card must be played regardless of legally
    playFaceUp player topCard = if null (sMinimum (validPlays topCard (faceUp player))) 
      then sMinimum (faceUp player) 
      else sMinimum (validPlays topCard (faceUp player))
    
    sMinimum [] = []--a safe minimum for cards that returns result in a list
    sMinimum xs = [minimumBy (compare `on` rank) xs]

    sRemove xs [] = xs-- a safe remove for both list and target
    sRemove xs [t] = [x | x<-xs, x /= t]



applyStrategy :: State GameState String
applyStrategy = do
  gs <- get
  
  let card = evalState callStrategy gs
      newGS =  execState callStrategy gs
      player = players newGS !! currentIx newGS
  --no legal move condition
  if null card || null (validPlays (maybeTopCard (discardPile gs)) card) then do
    put (execState (giveWastePileTo player) newGS){currentIx = incCI newGS}--picks up pile
    return ""
  --burn condition
  else if rank (head card) == R10 || fourInRow (head card) (discardPile newGS) (length card) then do
    let newBurnedPiles = (head card : discardPile newGS): burnedPiles newGS
        finalGS = execState (replenishCards player) newGS
    put finalGS{burnedPiles = newBurnedPiles,currentIx = incCI finalGS,discardPile=[]}
    return "Stack Burned\n"
  -- regular pace down
  else  do
    let newDiscardPile = card ++ discardPile newGS
        finalGS = execState (replenishCards player) newGS
    put finalGS{discardPile = newDiscardPile,currentIx = incCI finalGS}
    return ""
    where
      fourInRow _ _ 4 = True--checks if 4 cards of same value are in a row
      fourInRow _ [] _ = False
      fourInRow t (x:xs) count
        | rank t == rank x = fourInRow t xs (count+1)
        | rank x == R8 = fourInRow t xs count
        | otherwise = False

incCI :: GameState -> Int
incCI gs = (currentIx gs +1) `mod` length (players gs)

gameLoop :: State GameState [Int]
gameLoop = do
  gs <- get
  let n = roundNum gs
  if length (players gs) -1 <= length (finishedOrder gs) || n >= 1000 then do--base case
    put gs
    return (finishedOrder gs)
  --skip finished players
  else if pId (player gs) `elem` finishedOrder gs then do
    put (execState gameLoop gs{currentIx = incCI gs, roundNum = n + 1})
    return (evalState gameLoop gs{currentIx = incCI gs, roundNum = n + 1})
  else do
    let newGs = execState applyStrategy gs--executes player turn
    --if player is out
    if playerOut (lastPlayer newGs) then do
      let newFinishedOrder = finishedOrder newGs ++ [pId (lastPlayer newGs)]
      put (execState gameLoop newGs{finishedOrder = newFinishedOrder, roundNum = n + 1}) 
      return (evalState gameLoop newGs{finishedOrder = newFinishedOrder, roundNum = n + 1})
    --if player still in
    else do
      put (execState gameLoop newGs{roundNum = n + 1})
      return (evalState gameLoop newGs{roundNum = n + 1})

chooseStartingPlayer :: State GameState ()
chooseStartingPlayer = do
  gs <- get
  let ps = players gs--gets list of players
      --collects and sorts all hands according to there ranks
      cards = foldl (\hs p -> [sort [rank card| card<- hand p]] : hs) [] ps
      mini = minimum cards--gets the worst hand
      startingIndex = unwrap (elemIndex mini cards)--finds the index the worst hand is located at
  put gs{currentIx = startingIndex}
  return ()
  where
    unwrap (Just x) = x
    unwrap Nothing = 0
  
basicStrategySets:: State GameState Deck
basicStrategySets = do
  gs <- get
  let player = players gs !! currentIx gs
      topCard = maybeTopCard (discardPile gs)
  if (not.null) (hand player) then do--if there are cards in hand
    let cards = sMinimum (validPlays topCard (hand player))
    put gs{players = replacePlayer gs (player{hand = sRemove (hand player) cards})}
    return cards
  --no card in hand but cards in faceUp
  else if null (drawPile gs) && (not.null) (faceUp player) then do
    let cards = playFaceUp player topCard
    put gs{players = replacePlayer gs (player{faceUp = sRemove (faceUp player) cards})}
    return cards
  --no cards in hand or faceUp but faceDown
  else if null (drawPile gs) && null (faceUp player) && not (null (faceDown player)) then do
    let card = playFaceUp player topCard
    put gs{players = replacePlayer gs (player{faceDown = tail (faceDown player)})}
    return card
  --this is only here for safety if it runs player should have already been out
  else do
    put gs
    return []
  where
    --when playing faceUp cards a card must be played regardless of legally
    playFaceUp player topCard = if null (sMinimum (validPlays topCard (faceUp player))) 
      then sMinimum (faceUp player)
      else sMinimum (validPlays topCard (faceUp player))
    
    sMinimum [] = []--a safe minimum that returns results in a list
    sMinimum cards =  takeSet (sortBy (compare `on` rank) cards)

    --keeps taking cards from front of list until rank changes
    takeSet (x:xs) = x : takeWhile (\ y -> rank y == rank x) xs

    sRemove xs [] = xs--a safe remove for both list and target
    sRemove xs ts = [x | x<-xs, rank x /= rank (head ts)]




gameLoopWithHistory :: State GameState String
gameLoopWithHistory = do
  gs <- get
  let n = roundNum gs
  if length (players gs) -1 <= length (finishedOrder gs) || n == 1000 then do--base case
    put gs
    return (show (finishedOrder gs))
  --skip finished players
  else if pId (player gs) `elem` finishedOrder gs then do
    put (execState (gameLoopWithHistory) gs{currentIx = incCI gs,roundNum = n + 1})
    return (evalState (gameLoopWithHistory) gs{currentIx = incCI gs,roundNum = n + 1})
  else do
    let newGs = execState applyStrategy gs--executes player turn
        playerState = showPlayerState (player gs)
        
    --if player is out
    if playerOut(lastPlayer newGs) then do
      let newFinishedOrder = finishedOrder newGs ++ [pId (lastPlayer newGs)]
      put (execState (gameLoopWithHistory) newGs{finishedOrder = newFinishedOrder,roundNum = n + 1})

      return (showPlayerOut newGs{finishedOrder = newFinishedOrder, roundNum = n + 1} gs)
    --if player still in
    else do
      put (execState (gameLoopWithHistory) newGs{roundNum = n + 1})
      return (showPlayerOut newGs{roundNum = n +1} gs)
    
    
    
player :: GameState -> Player
player gs = players gs !! (currentIx gs `mod` length (players gs))

playerOut :: Player -> Bool
playerOut player = null (hand player) && null (faceUp player) && null (faceDown player)


lastPlayer :: GameState -> Player
lastPlayer gs | inc gs = ps !! ((ci - 1) `mod` numPs)
    | inc gs && pId (ps !! ((ci - 1) `mod` numPs)) `elem` fo = lastPlayer gs{currentIx = ci-1}
    | pId (ps !! ((ci + 1) `mod` numPs)) `elem` fo = lastPlayer gs{currentIx = ci+1}
    | otherwise = ps !! abs((ci + 1) `mod` numPs)
  where
    ps = players gs
    numPs = length ps
    ci = currentIx gs
    fo = finishedOrder gs

showPlayerIn :: GameState -> GameState -> String
showPlayerIn newGs gs = playerState ++ "\n" ++ (output ++ "\n" ++ recurse)
  where
    playerState = showPlayerState (player gs)
    output =  (show (discardPile newGs) ++ "\n")
    recurse = evalState applyStrategy gs ++ evalState gameLoopWithHistory newGs

showPlayerOut :: GameState -> GameState -> String
showPlayerOut newGs gs = playerState ++ "\n" ++ gameOutput ++ playerOut ++ "\n" ++ recurse
  where
    playerState = showPlayerState (player gs)
    gameOutput = (show (discardPile newGs)) ++ "\n" ++ evalState applyStrategy gs
    playerOut = pName (lastPlayer newGs) ++ " is Out \n"
    recurse = evalState (gameLoopWithHistory) newGs

--showPlayerIn ::

showPlayerState :: Player -> String--a helper function for displaying how the game is going
showPlayerState p = "Player " ++ pName p ++ showFaceDown p ++ showHand p  ++ showFaceUp p

showFaceDown :: Player -> String
showFaceDown player = " FaceDown: " ++ show (length (faceDown player))

showFaceUp :: Player -> String
showFaceUp player = "\n" ++ "FaceUp: " ++ show (faceUp player) 

showHand :: Player -> String--a helper function for displaying the players hand
showHand player = "\n" ++ "Hand: " ++ show (hand player)

callStrategy :: State GameState Deck--executes and evaluates strategy corresponding with player Id
callStrategy = do
  gs <- get
  let player = players gs !! currentIx gs
  put (execState (strategy player) gs)
  return (evalState (strategy player) gs)
  

playOneGameWithHistory :: IO ()
playOneGameWithHistory = do
  let myGen = mkStdGen 7--creates players and gen
      deck = [Card rank suit | rank<-[(minBound :: Rank)..],suit<-[(minBound :: Suit)..]]
      shuffledDeck = shuffleDeck myGen deck
      
      player1 = makePlayer 1 "testPlayer1" shuffledDeck basicStrategy
      player2 = makePlayer 2 "testPlayer2" (drop 9 shuffledDeck) basicStrategySets
      player3 = makePlayer 3 "testPlayer3" (drop 18 shuffledDeck) smartStrategy
  
  --creates new game state
  let gs = GameState [player1,player2,player3] 0 (drop 27 shuffledDeck) [] [] myGen [] 0 True
  putStr (evalState (gameLoopWithHistory) $ execState chooseStartingPlayer gs)


newCI :: GameState -> [Extension] -> Int--increments index for step 4 games
newCI gs exts
  | inc gs = (currentIx gs + 1) `mod` length (players gs)
  | otherwise = abs((currentIx gs- 1) `mod` length (players gs))


gameLoopWithHistory4 :: [Extension] -> State GameState String
gameLoopWithHistory4 exts = do
  gs <- get
  let n = roundNum gs
  --base case
  if length (players gs) -1 <= length (finishedOrder gs) || n == 1000 then do
    put gs
    return (show (finishedOrder gs))
  --skip finished players
  else if pId (player gs) `elem` finishedOrder gs then do
    put (execState (gameLoopWithHistory4 exts) gs{currentIx = newCI gs exts ,roundNum = n+1})
    return (evalState (gameLoopWithHistory4 exts) gs{currentIx = newCI gs exts ,roundNum = n+1})
  else do
    let newGs = execState (applyStrategy4 exts) gs{roundNum = n+1}
        --newInc = evalState (applyStrategy4 exts) gs
    --if player is out print
    if playerOut(lastPlayer newGs) then do
      let newFO = finishedOrder newGs ++ [pId (lastPlayer newGs)]
      put (execState (gameLoopWithHistory4 exts) newGs{finishedOrder = newFO})
      return (showPlayerOut4 gs newGs{finishedOrder = newFO} exts)
    --if player still in print
    else do
      put (execState (gameLoopWithHistory4 exts) newGs)
      return (showPlayerIn4 gs newGs exts)

showPlayerOut4 :: GameState -> GameState -> [Extension] -> String
showPlayerOut4 gs newGs exts = playerState ++ "\n" ++ gameOutput ++ playerOut ++ "\n" ++ recurse
  where
    playerState = showPlayerState (player gs)
    gameOutput = (show (discardPile newGs) ++ "\n")  ++ evalState (applyStrategy4 exts) gs ++ "\n"
    playerOut = pName (lastPlayer newGs) ++ " is Out \n"
    recurse = evalState (gameLoopWithHistory4 exts) newGs

  
showPlayerIn4 :: GameState -> GameState -> [Extension] -> String
showPlayerIn4 gs newGs exts = playerState ++ "\n" ++ gameOutput ++ "\n" ++ recurse
  where
    playerState = showPlayerState (player gs)
    gameOutput = (show (discardPile newGs) ++ "\n") ++ evalState (applyStrategy4 exts) gs
    recurse = evalState (gameLoopWithHistory4 exts) newGs

   
hasBurned :: GameState -> GameState -> Bool -> String --checks if stack has burned and returns appropriate string
hasBurned gs newGs inc =
  if null (discardPile newGs) && length(hand (player gs)) >= length(hand (lastPlayer newGs))
  then "Stack Burned\n" 
  else ""

applyStrategy4 :: [Extension] -> State GameState String
applyStrategy4 exts = do
  gs <- get
  
  let cards = evalState callStrategy gs
      newGS =  execState callStrategy gs
      p = player newGS
      i = inc gs
      newI = newInc i exts cards

  --no legal move condition
  if null cards || null (validPlays (maybeTopCard (discardPile gs)) cards) then do
    put (execState (giveWastePileTo p) newGS){currentIx = newCI newGS exts}--picks up pile
    return ""
  --burn condition
  else if rank (head cards) == R10 || fourInRow (head cards) (discardPile newGS) (length cards) then do
    let newBurnedPiles = (head cards : discardPile newGS): burnedPiles newGS
        finalGS = execState (replenishCards (player newGS)) newGS
    put finalGS{burnedPiles = newBurnedPiles,currentIx = newCI finalGS{inc = newI} exts,discardPile=[]}
    return "Stack Burned\n" 
  --regular pace down
  else  do
    let newDiscardPile = cards ++ discardPile newGS
        index = newCI newGS{inc = newI} exts
        --finalGS = execState (replenishCards p) newGS{inc = newI}

    --if three 3s played if extension is on
    if extention3 exts cards then  do
      let finalGS = execState applyExtention3 newGS{discardPile = newDiscardPile}
          
      put (execState (replenishCards p) finalGS{inc = newI, currentIx = index})
      return "Three 3s played\n"
    --if 9 of clubs played if extension is on
    else if extention9 exts cards then do 
      let finalGS = execState applyExtention9 newGS{discardPile = newDiscardPile}
      put (execState (replenishCards (player finalGS)) finalGS{inc = newI, currentIx = index})
      return "9 of Clubs Played\n"
    --normal play
    else do
      let finalGS = execState (replenishCards p) newGS{inc = newI}
      put finalGS{discardPile = newDiscardPile,currentIx = index}
      return ""
    where
      sHead [] = []
      sHead (x:_) = [x]

      sTail [] = []
      sTail (_:xs) = xs
      
      --checks for extension conditions
      extention3 exts cards = ExtThree3s `elem` exts && length cards == 3 && rank (head cards) == R3
      extention9 exts cards = ExtNineClubs `elem` exts && Card R9 Clubs `elem` cards

      newInc inc exts cards--if odd number of 8 played reverse direction
        | ExtReverse8 `elem` exts && odd (length cards) = not inc && rank (head cards) == R8
        | otherwise = inc
                      
      fourInRow _ _ 4 = True--if four cards of same rank in a row
      fourInRow _ [] _ = False
      fourInRow t (x:xs) count
        | rank t == rank x = fourInRow t xs (count+1)
        | rank x == R8 = fourInRow t xs count
        | otherwise = False

nextPlayer :: GameState -> Player
nextPlayer gs | inc gs = ps !! ((ci + 1) `mod` numPs)
    | inc gs && pId (ps !! ((ci + 1) `mod` numPs)) `elem` fo = nextPlayer gs{currentIx = ci+1}
    | pId (ps !! ((ci - 1) `mod` numPs)) `elem` fo = nextPlayer gs{currentIx = ci-1}
    | otherwise = ps !! abs((ci -1) `mod` numPs)
  where
    ps = players gs
    numPs = length ps
    ci = currentIx gs
    fo = finishedOrder gs

applyExtention9 :: State GameState ()
applyExtention9 = do
  gs <- get
  let cardToSwap = sHead (hand (nextPlayer gs))
      newp = (nextPlayer gs){hand = sTail (hand (nextPlayer gs))}
      newps = replacePlayer gs newp
      p = player gs
      finalPs = replacePlayer gs{players = newps} (p{hand = hand p ++ cardToSwap})
  put gs{players = finalPs}
  return ()
  where
    sTail [] = []
    sTail (_:xs) = xs

    sHead [] = []
    sHead (x:_) = [x]

applyExtention3 :: State GameState ()
applyExtention3 = do 
  gs <- get
  let newp = (nextPlayer gs){hand = hand (nextPlayer gs) ++ (discardPile gs)}
      newps = replacePlayer gs newp
  put gs{discardPile = [], players = newps}
  return ()
   

smartStrategy :: State GameState Deck
smartStrategy = do
  gs <- get
  let player = players gs !! currentIx gs
      topCard = maybeTopCard (discardPile gs)
  if (not.null) (hand player) then do--if there are cards in hand
    let cards = sMinimum (validPlays topCard (hand player))
    put gs{players = replacePlayer gs (player{hand = sRemove (hand player) cards})}
    return cards
  --no card in hand but cards in faceUp
  else if null (drawPile gs) && (not.null) (faceUp player) then do
    let cards = playFaceUp player topCard
    put gs{players = replacePlayer gs (player{faceUp = sRemove (faceUp player) cards})}
    return cards
  --no cards in hand or faceUp but faceDown
  else if null (drawPile gs) && null (faceUp player) && not (null (faceDown player)) then do
    let card = [head (faceDown player)]
    put gs{players = replacePlayer gs (player{faceDown = tail (faceDown player)})}
    return card
  else do--this is only here for safety if it runs player should have already been out
    put gs
    return []
  where
    --when playing faceUp cards a card must be played regardless of legality
    playFaceUp player topCard = if null (sMinimum (validPlays topCard (faceUp player))) 
      then 
        sMinimum (faceUp player)--if no legal move
      else 
        sMinimum (validPlays topCard (faceUp player))--if legal move

    sMinimum [] = []--picks what card is best to play and in what quantity
    sMinimum cards = if rank (minimumBy (compare `on` rank) cards) > RQ
      then 
        [minimumBy (compare `on` rank) cards]--use highest cards sparingly
      else
        takeSet (sortBy (compare `on` rank) cards)--get rid of low rank cards quickly
    
    --keeps taking cards from front of list until rank changes
    takeSet (x:xs) = x : takeWhile (\ y -> rank y == rank x) xs

    sRemove xs ts = [x | x<-xs, x `notElem` ts]--removes a list of items from a list

playTournament :: Int -> IO [(String, Int)]
playTournament n = do 
  let results = (runGames n)
      --counts how many times each player won
      p1Count = length (filter (==1) results)
      p2Count = length (filter (==2) results)
      p3Count = length (filter (==3) results) 
      counts = [p1Count,p2Count,p3Count]
      list = (zip (map pName $ newPlayers 0) counts)--pairs counts with player names
  print list
  return list

    where
      runGames :: Int -> [Int]
      runGames 0  = []--runs n independent games and returns a list of the winners of length n
      runGames n = (take 1(evalState (gameLoop) $ newState n)) ++ (runGames (n-1))

      --creates a new game state
      tempState n = GameState (newPlayers n) 0 (drop 27 $ newDeck n) [] [] (mkStdGen n) [] 0 True
      newState n = execState chooseStartingPlayer $ tempState n
      basicPlayer n = makePlayer 1 "BasicPlayer" (newDeck n) basicStrategy
      setPlayer n = makePlayer 2 "SetPlayer" (drop 9 (newDeck n)) basicStrategySets
      smartPlayer n = makePlayer 3 "SmartPlayer" (drop 18 (newDeck n)) smartStrategy


      newPlayers n= [basicPlayer n,setPlayer n,smartPlayer n]
      tempDeck = [Card rank suit | rank<-[(minBound :: Rank)..],suit<-[(minBound :: Suit)..]]
      newDeck n = shuffleDeck (mkStdGen n) tempDeck


--a helper function for setting up new games
makePlayer :: PlayerId -> PlayerName -> Deck -> (State GameState Deck) -> Player
makePlayer id name deck strategy = Player id name hand faceUp faceDown strategy
  where
    hand = take 3 deck
    faceUp = take 3 $ drop 3 deck
    faceDown = take 3 $ drop 6 deck

playOneGame :: IO ()
playOneGame = do
  let myGen = mkStdGen 513--creates players and gen
      deck = [Card rank suit | rank<-[(minBound :: Rank)..],suit<-[(minBound :: Suit)..]]
      shuffledDeck = shuffleDeck myGen deck
      player1 = makePlayer 1 "testPlayer1" shuffledDeck basicStrategy
      player2 = makePlayer 2 "testPlayer2" (drop 9 shuffledDeck) basicStrategySets
      player3 = makePlayer 3 "testPlayer3" (drop 18 shuffledDeck) smartStrategy
  

  --creates new game state
  let gs =  GameState [player1,player2,player3] 0 (drop 27 shuffledDeck) [] [] myGen [] 0 True
  putStr (show $ evalState (gameLoop) $ execState chooseStartingPlayer gs)


playOneGameStep4 :: [Extension] -> IO ()
playOneGameStep4 exts = do
  let myGen = mkStdGen 10--creates players and gen
      deck = [Card rank suit | rank<-[(minBound :: Rank)..],suit<-[(minBound :: Suit)..]]
      shuffledDeck = shuffleDeck myGen deck
      player1 = makePlayer 1 "testPlayer1" shuffledDeck basicStrategy
      player2 = makePlayer 2 "testPlayer2" (drop 9 shuffledDeck) basicStrategySets
      player3 = makePlayer 3 "testPlayer3" (drop 18 shuffledDeck) smartStrategy
  
  --creates new game state
  let gs = GameState [player1,player2,player3] 0 (drop 27 shuffledDeck) [] [] myGen [] 0 True
  putStr (evalState (gameLoopWithHistory4 exts) $ execState chooseStartingPlayer gs)


main :: IO ()
main = do

  playTournament 100
  --playOneGameStep4 [ExtReverse8,ExtThree3s,ExtNineClubs]
  --playOneGame
  --playOneGameWithHistory
  putStr ("\n==========")