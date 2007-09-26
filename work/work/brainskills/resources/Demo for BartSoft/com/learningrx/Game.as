package com.learningrx
{
   import flash.display.*;
   import flash.utils.Timer;
   import flash.events.*;

   import com.learningrx.*;
   import com.learningrx.Screens.*;

   public class Game extends Sprite
   {
		public static const ROUND_TIMER_INTERVAL = 1000;

		public var _Name:String = 'None';

		protected var _Parent:Framework;
		protected var _Stage:Stage;
		protected var _RightAnswers:Number;
		protected var _WrongAnswers:Number;
		protected var _Turns:Class;
		protected var _Turn:Number;
		protected var _Level:Number;
		protected var _Sublevel:Number;
		protected var _Speed:Number;
		protected var _RoundDetails:Object;

		public function Game(pParent:Framework,
									pName:String,
									pTurns:Class)
		{
			_Parent = pParent;
			_Name = pName;
			_Turns = pTurns;
		}

		public function StartRound(pLevel:Number, 
											pSublevel:Number, 
											pSpeed:Number):void
		{
			ResetEverything();
			_Level = pLevel;
			_Sublevel = pSublevel;
			_Speed = pSpeed;
			_RoundDetails = _Turns.GetRound(pLevel, pSublevel, pSpeed);
		}
		
		public function OnStartRoundButtonClicked():void
		{
			this.focusRect = false;
			_Parent.stage.focus = this;
		}
		
		public function EndRound():void
		{
			_Parent.EndRound(_RightAnswers, _WrongAnswers);
		}
			
		public function ResetEverything():void
		{
			_RightAnswers = _WrongAnswers = 0;
			_Parent.UpdateScoreDisplay(0, 0);
			_Turn = -1; // Hack.
		}
		
		public function GetLevelsAndSublevels():Object
		{
			return _Turns.GetLevelsAndSublevels();
		}

		public function get Name():String
		{
			return _Name;
		}

		public function get Parent():Framework
		{
			return _Parent;
		}

		public function get NumberOfLevels():Number
		{
			return _Turns.NumberOfLevels;
		}

		public function get Level():Number
		{
			return _Level;
		}

		public function set Level(pLevel:Number):void
		{
			_Level = pLevel;
		}

		public function get Sublevel():Number
		{
			return _Sublevel;
		}

		public function set Sublevel(pSublevel:Number):void
		{
			_Sublevel = pSublevel;
		}

		public function get Turns():Class
		{
			return _Turns;
		}

		public function get BackgroundHeight():Number
		{
			
			return _Parent.GAME_HEIGHT;
		}

		public function get BackgroundWidth():Number
		{
			return _Parent.GAME_WIDTH;
		}

		public function get ScoreAndDividerY():Number
		{
			return _Parent.ScoreAndDividerY;
		}
		
		protected function PlayClick():void
		{
			_Parent.PlayClick();
		}

		protected function StartTimer(pTimer:Timer):void
		{
         if (pTimer != null)
			{
				pTimer.start();
			}
		}

		protected function StopTimer(pTimer:Timer):void
		{
         if (pTimer != null)
			{
				pTimer.stop();
			}
		}

		protected function ResetTimer(pTimer:Timer):void
		{
         if (pTimer != null)
			{
				pTimer.reset();
			}
		}

		protected function RestartTimer(pTimer:Timer):void
		{
         ResetTimer(pTimer);
			StartTimer(pTimer);
		}

		protected function Show(...args):void
		{
			for (var i:Number = 0; i < args.length; ++i)
			{
				Utilities.AddChildToDisplayList(this, args[i]);
			}
		}

		protected function Hide(...args):void
		{
			for (var i:Number = 0; i < args.length; ++i)
			{
				Utilities.RemoveChildFromDisplayList(this, args[i]);
			}
		}
	}
}