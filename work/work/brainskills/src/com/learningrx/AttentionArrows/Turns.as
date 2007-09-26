package com.learningrx.AttentionArrows
{
	import com.learningrx.*;

	public class Turns
	{
		private static var _RulesAndDefs:Class = com.learningrx.AttentionArrows.RulesAndDefinitions;
		private static var _CurrentFactor:String = null;
		private static var _Game:Game;
		
		public static function set Game(pGame:Game):void
		{
			_Game = pGame;
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

		public static function get Levels():Object
		{
			return _RulesAndDefs.LEVELS;
		}

		public static function get NumberOfLevels():Number
		{
			return Utilities.ObjectLength(_RulesAndDefs.LEVELS);
		}
		
		public static function get Rotations():Object
		{
			return _RulesAndDefs.ROTATIONS;
		}
		
		public static function GetArrowColorValue(pColor:String):Object
		{
			return _RulesAndDefs.ARROW_COLOR_VALUES[pColor];
		}
		
		public static function get MovingArrowEaseOutPercent():Number
		{
			return _RulesAndDefs.MOVING_ARROW_EASE_OUT_PERCENT;
		}
		
		public static function get AudioDistractionsRate():Number
		{
			return _RulesAndDefs.AUDIO_DISTRACTIONS_RATE;
		}
		
		public static function get MetronomeTimerInterval():Number
		{
			return _RulesAndDefs.METRONOME_TIMER_INTERVAL;
		}
		
		public static function GetArrowsPerRound(pSpeed:Number):Number
		{
			return _RulesAndDefs.SPEEDS[pSpeed].ArrowsPerRound;
		}
		
		public static function GetMilliSecondsPerBeat(pSpeed:Number):Number
		{
			return _RulesAndDefs.SPEEDS[pSpeed].MilliSecondsPerBeat;
		}
		
		public static function get ArrowKeyCodes():Number
		{
			return _RulesAndDefs.ARROW_KEY_CODES;
		}
		
		public static function GetRandomArrowColor():String
		{
			return _RulesAndDefs.ARROW_COLORS[Utilities.RandRange(0, 3)];
		}
		
		public static function GetRandomDirection():String
		{
			return _RulesAndDefs.DIRECTIONS[Utilities.RandRange(0, 3)];
		}
		
		public static function GetOppositeDirection(pDirection:String):String
		{
			if (null == pDirection)
			{
				return null;
			}
			return _RulesAndDefs.OPPOSITE_DIRECTIONS[pDirection];
		}
		
		public static function GetClickWindow(pMillisecondsPerBeat:Number):Number
		{
			return _RulesAndDefs.CLICK_WINDOWS[pMillisecondsPerBeat];
		}
		
		public static function get DistractionArrowSpinSpeed():Number
		{
			return _RulesAndDefs.DISTRACTION_ARROW_SPIN_SPEED;
		}
		
		public static function GetDistractionDetails(pLevel:Number, 
														         pSublevel:Number):Object
		{
			var distractionDetails:Object = _RulesAndDefs.LEVELS[pLevel].Distractions;
			distractionDetails['ShowDistractions'] = _RulesAndDefs.LEVELS[pLevel].Sublevels[pSublevel].ShowDistractions;
			return distractionDetails;
		}
		
		public static function PlayAudibleBeat(pLevel:Number):Boolean
		{
			return (true == _RulesAndDefs.LEVELS[pLevel].Metronome); // I kept getting error messages if I didn't do this 
		}
		
		public static function GetTurnDetails(pLevel:Number, 
														  pSublevel:Number,
														  pPreviousColor:String,
														  pPreviousOrientation:String,
														  pPreviousMotion:String,
														  pSpeed:Number,
														  pTurn:Number):Object
		{
			var turnDetails:Object = new Object;
			do
			{
				turnDetails.Color = GetRandomArrowColor();
				turnDetails.Orientation = GetRandomDirection();
			}
			while (turnDetails.Color == pPreviousColor && turnDetails.Orientation == pPreviousOrientation);
			turnDetails.Motion = null;
			if (_RulesAndDefs.LEVELS[pLevel].Sublevels[pSublevel].Motion)
			{
				turnDetails.Motion = GetRandomDirection();
			}
			turnDetails.Answer = GetAnswer(pLevel, pSublevel, turnDetails.Color, 
													 pPreviousColor, turnDetails.Orientation, turnDetails.Motion, pTurn);
			turnDetails.TurnsPerRound = GetArrowsPerRound(pSpeed);
			turnDetails.MilliSecondsPerBeat = GetMilliSecondsPerBeat(pSpeed);
			return turnDetails;
		}
		
		private static function GetAnswer(pLevel:Number, 
													 pSublevel:Number,
													 pColor:String,
													 pPreviousColor:String,
													 pOrientation:String,
													 pMotion:String,
													 pTurn:Number):String
		{
			var answerType:String = _RulesAndDefs.LEVELS[pLevel].AnswerType;
			var factor:String = _RulesAndDefs.LEVELS[pLevel].Sublevels[pSublevel].Factor;
			var answer:String;
			if (pTurn == 0) // means this is turn # 1 in the round
			{
				_CurrentFactor = "Motion";
			}
			switch (answerType)
			{
				case "Same":
					answer = GetSame(factor, pOrientation, pMotion);
					break;
				case "Opposite":
					answer = GetOpposite(factor, pOrientation, pMotion);
					break;
				case "OppositeOnRedOrGreen":
					answer = GetOppositeOnRedOrGreen(factor, pColor, pOrientation, pMotion);
					break;
				case "Clockwise":
					answer = GetClockwise(factor, pOrientation, pMotion);
					break;
				case "ClockwiseOnBlueOrYellow":
					answer = GetClockwiseOnBlueOrYellow(factor, pColor, pOrientation, pMotion);
					break;
				case "OppositeIfColorEqualsPrevious":
					answer = GetOppositeIfColorEqualsPrevious(factor, pColor, pOrientation, pMotion, pPreviousColor);
					break;
				case "Pattern":
					answer = GetPattern(factor, pTurn, pOrientation, pMotion);
					break;
				case "SameIfOrientationEqualsMotion":
					answer = GetSameIfOrientationEqualsMotion(pOrientation, pMotion);
					break;
				case "SwitchOnRed":
					answer = GetSwitchOnRed(pColor, pOrientation, pMotion, pCurrentFactor);
					break;
				case "SameIfOrientationEqualsMotionClockwiseOnRed":
					answer = GetSameIfOrientationEqualsMotionClockwiseOnRed(pOrientation, pMotion);
					break;
				case "SameIfOrientationEqualsMotionClockwiseIfColorEqualsPrevious":
					answer = GetSameIfOrientationEqualsMotionClockwiseIfColorEqualsPrevious(pColor, 
											pOrientation, pMotion, pPreviousColor);
					break;
			}
			return answer;
		}
		
		private static function GetSame(pFactor:String,
												  pOrientation:String,
												  pMotion:String):String
		{
			if (pFactor == "Orientation")
			{
				return pOrientation;
			}
			return pMotion;
		}
		
		private static function GetOpposite(pFactor:String,
													   pOrientation:String,
												      pMotion:String):String
		{
			return GetOppositeDirection(GetSame(pFactor, pOrientation, pMotion));
		}
		
		private static function GetOppositeOnRedOrGreen(pFactor:String,
																      pColor:String,
																	   pOrientation:String,
																	   pMotion:String):String
		{
			if (ArrayContains(['red', 'green'], pColor))
			{
				return GetOpposite(pFactor, pOrientation, pMotion);
			}
			else
			{
				return GetSame(pFactor, pOrientation, pMotion);
			}
		}
		
		private static function GetClockwise(pFactor:String,
														 pOrientation:String,
												       pMotion:String):String
		{
			return _RulesAndDefs.CLOCKWISE_DIRECTIONS[GetSame(pFactor, pOrientation, pMotion)];
		}
		
		private static function GetClockwiseOnBlueOrYellow(pFactor:String,
														               pColor:String,
																		   pOrientation:String,
																		   pMotion:String):String
		{
			if (Utilities.ArrayContains(['blue', 'yellow'], pColor))
			{
				return GetClockwise(pFactor, pOrientation, pMotion);
			}
			else
			{
				return GetSame(pFactor, pOrientation, pMotion);
			}
		}
		
		private static function GetOppositeIfColorEqualsPrevious(pFactor:String,
																				   pColor:String,
																				   pPreviousColor:String,
																				   pOrientation:String,
																				   pMotion:String):String
		{
			if (pPreviousColor == pColor)
			{
				return GetOpposite(pFactor, pOrientation, pMotion);
			}
			else
			{
				return GetSame(pFactor, pOrientation, pMotion);
			}
		}
		
		private static function GetPattern(pFactor:String,
													  pTurn:String,
												     pOrientation:String,
												     pMotion:String):String
		{
			switch (pFactor)
			{
				case "OrientationEveryThird":
					if (pTurn % 3 == 0)
					{
						_CurrentFactor = GetOppositeFactor(_CurrentFactor);
					}
					break;
				case "OrientationEveryOther":
					if (pTurn % 2 == 0)
					{
						_CurrentFactor = GetOppositeFactor(_CurrentFactor);
					}
					break;
			}
			return GetSame(_CurrentFactor, pOrientation, pMotion);
		}
		
		private static function GetSameIfOrientationEqualsMotion(pOrientation:String,
																				   pMotion:String):String
		{
			if (pOrientation == pMotion)
			{
				return GetSame("Orientation", pOrientation, pMotion);
			}
			else
			{
				return GetOpposite("Orientation", pOrientation, pMotion);
			}
		}
		
		private static function GetSwitchOnRed(pColor:String,
												         pOrientation:String,
												         pMotion:String):String
		{
			if ('red' == pColor)
			{
				_CurrentFactor = GetOppositeFactor(_CurrentFactor);
			}
			return GetSame(_CurrentFactor, pOrientation, pMotion);
		}
		
		private static function GetSameIfOrientationEqualsMotionClockwiseOnRed(pOrientation:String,
																									  pMotion:String):String
		{
			var answer:String = GetSameIfOrientationEqualsMotion(pColor, pOrientation, pMotion);
			if ('red' == pColor)
			{
				answer =  _RulesAndDefs.CLOCKWISE_DIRECTIONS[answer];
			}
			return answer;
		}
		
		private static function GetSameIfOrientationEqualsMotionClockwiseIfColorEqualsPrevious(pColor:String,
																														   pOrientation:String,
																														   pMotion:String,
																														   pPreviousColor:String):String
		{
			var answer:String = GetSameIfOrientationEqualsMotion(pColor, pOrientation, pMotion);
			if (pPreviousColor == pColor)
			{
				answer = _RulesAndDefs.CLOCKWISE_DIRECTIONS[answer];
			}
			return answer;
		}
		
		private static function GetOppositeFactor(pFactor:String):String
		{
			if ("Orientation" == pFactor)
			{
				return "Motion";
			}
			return "Orientation";
		}
		
		public static function FeedbackCheck(pConsecutiveWrongAnswers:Number,
													    pConsecutiveRightAnswers:Number):void
		{
			if (_Game.GlobalVolume < _RulesAndDefs.MAXIMUM_VOLUME && 
											pConsecutiveWrongAnswers >= _RulesAndDefs.CONSECUTIVE_ERRORS_FOR_VOLUME_INCREASE)
			{
				_Game.GlobalVolume = Math.max(_RulesAndDefs.MAXIMUM_VOLUME,  _RulesAndDefs.MINIMUM_VOLUME + 
				                     Math.floor(pConsecutiveWrongAnswers / 2) *  _RulesAndDefs.VOLUME_CHANGE_FACTOR);
			}
			else if (_Game.GlobalVolume > _RulesAndDefs.MINIMUM_VOLUME && 
						pConsecutiveRightAnswers >= _RulesAndDefs.CONSECUTIVE_RIGHT_ANSWERS_FOR_VOLUME_DECREASE)
			{
				_Game.GlobalVolume = _Game.GlobalVolume - _RulesAndDefs.VOLUME_CHANGE_FACTOR;
			}
		}
	}
}