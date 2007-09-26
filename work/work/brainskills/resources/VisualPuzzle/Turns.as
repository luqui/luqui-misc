package com.learningrx.VisualPuzzle
{
	import com.learningrx.Shared.*;

	public class Turns
	{
		private static var _RulesAndDefs:Class = com.learningrx.VisualPuzzle.RulesAndDefinitions;
		
		public static function get NumberOfLevels():Number
		{
			return Utilities.ObjectLength(_RulesAndDefs.LEVELS);
		}
		
		public static function GetNumberOfSpeeds(pLevel:Number,
															  pSublevel:Number):Number
		{
			return Utilities.ObjectLength(_RulesAndDefs.SPEEDS);
		}

		public static function GetInstructions(pLevel:Number,
															pSublevel:Number):String
		{
			return _RulesAndDefs.INSTRUCTIONS[pLevel].Sublevels[pSublevel];
		}

		public static function get DisplayTimerInterval():Number
		{
			return _RulesAndDefs.DISPLAY_TIMER_INTERVAL;
		}
		
		public static function get AnimateTimerInterval():Number
		{
			return _RulesAndDefs.ANIMATE_TIMER_INTERVAL;
		}

		public static function get IntervalTimerInterval():Number
		{
			return _RulesAndDefs.INTERVAL_TIMER_INTERVAL;
		}
		
		public static function get Levels():Object
		{
			return _RulesAndDefs.LEVELS;
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

		public static function GetEdges(pShapeStyle:String):Array
		{
			return _RulesAndDefs.EDGES[pShapeStyle];
		}

		public static function GetRound(pLevel:Number,
												  pSublevel:Number,
												  pSpeed:Number)
		{
			var roundDetails:Object = new Object;
			var level:Object = _RulesAndDefs.LEVELS[pLevel];
			roundDetails.Edges = _RulesAndDefs.EDGES[level.ShapeStyle];
			roundDetails.MaximumRotation = level.MaximumRotation;
			roundDetails.Flipping = level.Flipping;
			roundDetails.Backside = level.Backside;
			roundDetails.ImageFileName = level.ImageFileName;
			roundDetails.Columns = level.Columns;
			roundDetails.Rows = level.Rows;
			roundDetails.Behavior = level.Sublevels[pSublevel];
			roundDetails.TimePerPiece = _RulesAndDefs.SPEEDS[pSpeed].TimePerPiece + (pLevel * _RulesAndDefs.TIME_PER_LEVEL_ADJUSTMENT);
			roundDetails.Time = roundDetails.TimePerPiece * roundDetails.Columns * roundDetails.Rows;
			return roundDetails;
		}
	}
}
