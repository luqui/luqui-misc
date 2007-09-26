package com.learningrx.FixationNumbers
{
	import com.learningrx.*;

	public class Turns
	{
		private static var _RulesAndDefs:Class = com.learningrx.FixationNumbers.RulesAndDefinitions;
		
		public static function get NumberOfLevels():Number
		{
			return Utilities.ObjectLength(_RulesAndDefs.LEVELS);
		}
		
		public static function get Levels():Object
		{
			return _RulesAndDefs.LEVELS;
		}

		public static function get Speeds():Object
		{
			return _RulesAndDefs.SPEEDS;
		}

		public static function get TurnsPerRound():Number
		{
			return _RulesAndDefs.TURNS_PER_ROUND;
		}
		
		public static function get DisplayTimerInterval():Number
		{
			return _RulesAndDefs.DISPLAY_TIMER_INTERVAL;
		}
		
		public static function get IntervalTimerInterval():Number
		{
			return _RulesAndDefs.INTERVAL_TIMER_INTERVAL;
		}
		
		public static function get NumberColorValues():Object
		{
			return _RulesAndDefs.NUMBER_COLOR_VALUES;
		}
		
		public static function GetRandomNumberColorValue():Number
		{
			return NumberColorValues[GetRandomNumberColor()];
		}
		
		public static function GetRandomNumberColor():String
		{
			return _RulesAndDefs.NUMBER_COLORS[Utilities.RandRange(0, 3)];
		}
		
		public static function GetRow(pTurn:Number,
												pLevel:Number,
												pSublevel:Number):Number
		{
			switch (_RulesAndDefs.LEVELS[pLevel].Sublevels[pSublevel][pTurn % 2])
			{
				case "Top":
					return Math.floor(pTurn / 2) % 5;
					break;
				case "Bottom":
					return (TurnsPerRound / 2 - Math.floor(pTurn / 2)) % 5;
					break;
				case "Random":
					return (Utilities.RandRange(TurnsPerRound / 2 * .125, TurnsPerRound / 2 * .875)) % 5;
					break;
			}
		}
		
		public static function GetLevelsAndSublevels():Object
		{
			var sublevels:Object = new Object();
			sublevels.NumberOfLevels = NumberOfLevels;
			for (var i:Number = 1; i <= NumberOfLevels; ++i)
			{
				sublevels[i] = GetNumberOfSublevels(i);
			}
			return sublevels;
		}

		public static function GetNumberOfSublevels(pLevel:Number):Number
		{
			return Utilities.ObjectLength(Levels[pLevel].Sublevels);
		}

		public static function GetRound(pLevel:Number, 
												  pSublevel:Number,
												  pSpeed:Number)
		{
			var ruleDetails:Object = GetRuleDetails(Levels[pLevel].AnswerType);
			var roundDetails:Object = new Object;
			roundDetails.ShowCircle = false;
			roundDetails.TargetNumber = ruleDetails.TargetNumber;
			if (Levels[pLevel].AnswerType == "CircledNumbers")
			{
				roundDetails.ShowCircle = true;
			}
			roundDetails.DisplayMilliseconds = Speeds[pSpeed].Display;
			roundDetails.IntervalMilliseconds = Speeds[pSpeed].Interval;
			roundDetails.NumOfAnswers = Levels[pLevel].NumberOfResponses;
			roundDetails.Hint = FormatHintString(Levels[pLevel].Hint, ruleDetails.TargetNumber);
			roundDetails.Turns = CreateTurns(InitTurns(pLevel, pSublevel),
														ruleDetails.TurnOffset, 
														ruleDetails.AnswerOffset,
														roundDetails.NumOfAnswers,
														ruleDetails.TargetNumber,
														ruleDetails.Red);
			return roundDetails;
		}
			
		private static function InitTurns(pLevel:Number,
													pSublevel:Number):Array
		{
			var turns:Array = new Array();
			for (var i:Number = 0; i < TurnsPerRound; ++i)
			{
				turns.push(
				{
					Number: NaN, 
					Color: NaN,
					Answer: NaN,
					Column: i % 2,
					Row: GetRow(i, pLevel, pSublevel)
				});
			}
			return turns;
		}

		private static function CreateTurns(pTurns:Array,
													  pTurnOffset:Number,
													  pAnswerOffset:Number,
													  pNumOfAnswers:Number,
													  pTargetNumber:Number,
													  pRedRound:Boolean):Array
		{
			var turns:Array = pTurns;
			var answerNumbers:Array = InitAnswerNumbers(pNumOfAnswers, pTurnOffset);
			var targetNumberRound:Boolean = !isNaN(pTargetNumber);
			for (var i:Number = 0; i < TurnsPerRound; ++i)
			{
				if (isNaN(pTurns[i].Number)) // Has a previous pass through this loop already set the Number?
				{
					turns[i].Number = Utilities.RandRange(0, 9);
				}
				if (isNaN(turns[i].Color)) // Has a previous pass through this loop already set the Color?
				{
					do 
					{
						turns[i].Color = GetRandomNumberColorValue();
					}
					while (pRedRound && NumberColorValues["red"] == turns[i].Color)
				}
				if (Utilities.ArrayContains(answerNumbers, i))
				{
					if (pTurnOffset > 0 || !Utilities.ArrayContains(answerNumbers, i + pTurnOffset))
					{
						do
						{
							turns[i].Number = Utilities.RandRange(0, 9 - Math.max(0, pAnswerOffset));
						} 
						while (targetNumberRound && pTargetNumber == turns[i].Number)
					}
					if (pRedRound)
					{
						turns[i - pTurnOffset].Color = NumberColorValues["red"];
						turns[i - pTurnOffset].Number = Utilities.RandRange(0, 9 - Math.max(0, pAnswerOffset));
					}
					else if (targetNumberRound)
					{
						turns[i - pTurnOffset].Number = pTargetNumber;
						if (Utilities.ArrayContains(answerNumbers, i - pTurnOffset))
						{
							turns[i - pTurnOffset].Answer = turns[i - pTurnOffset].Number + pAnswerOffset;
						}
					}
					turns[i - Math.min(0, pTurnOffset)].Answer = Math.abs(turns[i].Number + pAnswerOffset);
				}
			}
			return turns;
		}

		private static function GetRuleDetails(pAnswerType:String):Object
		{
			var red:Boolean = false;
			var turnOffset:Number = 0;
			var answerOffset:Number = 0;
			var targetNumber:Number = NaN;
			switch (pAnswerType)
			{
				case "RedNumber":
					red = true;
					break;
				case "OneAfterRedNumber":
					red = true;
					turnOffset = 1;
					break;
				case "OneBeforeRedNumber":
					red = true;
					turnOffset = -1;
					break;
				case "OneAfterRedNumberPlus1":
					red = true;
					turnOffset = 1;
					answerOffset = 1;
					break;
				case "OneBeforeRedNumberPlus3":
					red = true;
					turnOffset = -1;
					answerOffset = 3;
					break;
				case "OneBeforeRedNumberDifference3":
					red = true;
					turnOffset = -1;
					answerOffset = -3;
					break;
				case "OneAfterTargetNumber":
					turnOffset = 1;
					targetNumber = Utilities.RandRange(0, 9);
					break;
				case "OneBeforeTargetNumber":
					turnOffset = -1;
					targetNumber = Utilities.RandRange(0, 9);
					break;
				case "OneAfterTargetNumberPlus2":
					turnOffset = 1;
					answerOffset = 2;
					targetNumber = Utilities.RandRange(0, 9 - answerOffset);
					break;
				case "OneBeforeTargetNumberDifference4":
					turnOffset = -1;
					answerOffset = -4;
					targetNumber = Utilities.RandRange(0, 9);
					break;
				case "OneBeforeTargetNumberDifference9":
					turnOffset = -1;
					answerOffset = -9;
					targetNumber = Utilities.RandRange(0, 9);
					break;
			}
			var ruleDetails:Object = 
			{
				Red: red, 
				TurnOffset: turnOffset, 
				AnswerOffset: answerOffset, 
				TargetNumber: targetNumber
			};
			return ruleDetails;
		}
		
		private static function InitAnswerNumbers(pNumOfAnswers:Number,
																pTurnOffset:Number):Array
		{
			var answerNumbers:Array = new Array();
			if (pTurnOffset > 0)
			{
				answerNumbers = GetUniqueRandomNumbers(pNumOfAnswers, TurnsPerRound - 1, [0, 1]);
			}
			else if (pTurnOffset < 0)
			{
				answerNumbers = GetUniqueRandomNumbers(pNumOfAnswers, TurnsPerRound - 1, 
																	[TurnsPerRound - 2, TurnsPerRound - 1]);
			}
			else
			{
				answerNumbers = GetUniqueRandomNumbers(pNumOfAnswers, TurnsPerRound - 1, []);
			}
			
			return answerNumbers;
		}

		private static function FormatHintString(pHint:String,
															  pTargetNumber:Number):String
		{
			if (8 == pTargetNumber)
			{
				return pHint.replace('TARGET', 'an ' + pTargetNumber.toString());
			}
			return pHint.replace('TARGET', 'a ' + pTargetNumber.toString());
		}
		
		private static function GetUniqueRandomNumbers(pNumberOfRandomNumbers:Number,
																	  pMaxNumberToChooseFrom:Number,
																	  pNumbersToExclude:Array):Array
		{
			var randomNumbers:Array = [];
			var nextNumber:Number;
			for (var i:Number = 0; i < pNumberOfRandomNumbers; ++i)
			{
				do
				{
					nextNumber = Utilities.RandRange(0, pMaxNumberToChooseFrom);
				}
				while (Utilities.ArrayContains(pNumbersToExclude, nextNumber))
				randomNumbers.push(nextNumber);
				pNumbersToExclude.push(nextNumber);
			}
			randomNumbers.sort(Array.NUMERIC);
			return randomNumbers;
		}
	}
}