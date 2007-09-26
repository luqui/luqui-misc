package com.learningrx.FixationNumbers
{
	import flash.display.*;
	import flash.events.*;
	import flash.utils.Timer;

	import com.learningrx.*
	import com.learningrx.Screens.*
	
	public class FixationNumbers extends Game
	{
		private var _NumberKeyHandler:NumberKeyHandler;
		private var _NumberSprite:NumberSprite;
		private var _NumberButtons:NumberButtons;
		private var _ResultsText:ResultsText;
		private var _HintBox:HintBox;
		private var _NumberSpriteHeight:Number;
		private var _RightAnswer:Number;
		private var _DisplayTimer:Timer;
		private var _IntervalTimer:Timer;
		private var _Answered:Boolean;
		
		public function FixationNumbers(pParent:Framework)
		{
			super(pParent, 'FixationNumbers', com.learningrx.FixationNumbers.Turns);
			_NumberKeyHandler = new NumberKeyHandler(this);
			_NumberSpriteHeight = 150;
			_NumberSprite = new NumberSprite(this);
			_HintBox = new HintBox(this);
			_HintBox.x = BackgroundWidth - _HintBox.width - 20;
			_HintBox.y = 20;
			_NumberButtons = new NumberButtons(this);
			_NumberButtons.x = BackgroundWidth - _NumberButtons.width - 20;
			_NumberButtons.y = _Parent.ScoreAndDividerY - _NumberButtons.height - 20;
		}

		override public function StartRound(pLevel:Number, 
														pSublevel:Number, 
														pSpeed:Number):void
		{
			super.StartRound(pLevel, pSublevel, pSpeed);
			InitDisplayTimer(_RoundDetails.DisplayMilliseconds);
			InitIntervalTimer(_RoundDetails.IntervalMilliseconds);
			DisplayHint();
			Show(_NumberButtons, _HintBox);
			_Parent.ShowScoreAndDivider(true);
		}
		
		override public function OnStartRoundButtonClicked():void
		{
			super.OnStartRoundButtonClicked();
			_NumberKeyHandler.Enable();
			StartTurn();
		}
		
		override public function EndRound():void
		{
			Hide(_NumberButtons, _HintBox);
			_NumberKeyHandler.Disable();
			super.EndRound();
		}
			
		override public function ResetEverything():void
		{
			StopTimer(_IntervalTimer);
			StopTimer(_DisplayTimer);
			Hide(_NumberSprite, _ResultsText);
			super.ResetEverything();
		}
		
		private function StartTurn():void
		{
			++_Turn;
			if (_Turn >= _Turns.TurnsPerRound)
			{
				EndRound();
			}
			else
			{
				_Answered = false;
				DisplayNextNumber();
			}
		}
		
		private function DisplayNextNumber():void
		{
         StartTimer(_DisplayTimer);
			_RightAnswer = _RoundDetails.Turns[_Turn].Answer;
			_NumberSprite.DisplayNumber = _RoundDetails.Turns[_Turn].Number;
			_NumberSprite.DisplayColor = _RoundDetails.Turns[_Turn].Color;
			if (_RoundDetails.ShowCircle)
			{
				if (isNaN(_RightAnswer))
				{
					_NumberSprite.HideOutline();
				}
				else
				{
					_NumberSprite.ShowOutline();
				}
			}
			else
			{
				_NumberSprite.HideOutline();
			}
			Show(_NumberSprite);
			PositionNumberSprite(_Turn);
		}

		public function OnNumberClicked(pNumber:Number):void
		{
			if (!_Answered)
			{
				if (pNumber == _RightAnswer)
				{
					++_RightAnswers;
				}
				else
				{
					++_WrongAnswers;
				}
				_Parent.UpdateScoreDisplay(_RightAnswers, _WrongAnswers);
				_Answered = true;
			}
		}
		
		private function PositionNumberSprite(pTurn:Number):void
		{
			if (0 == _RoundDetails.Turns[pTurn].Column)
			{
				_NumberSprite.x = (BackgroundWidth - _NumberSprite.width) * .2;
			}
			else
			{
				_NumberSprite.x = (BackgroundWidth - _NumberSprite.width) * .55;
			}
			_NumberSprite.y = (_RoundDetails.Turns[pTurn].Row * (_Parent.ScoreAndDividerY - 50)) / 5;
		}

		private function DisplayHint()
		{
			if (!isNaN(_RoundDetails.TargetNumber))
			{
				_RoundDetails.Hint = _RoundDetails.Hint.replace("TARGET", _RoundDetails.TargetNumber.toString());
			}
			_HintBox.DisplayHint(_RoundDetails.Hint);
		}
		
		// Getter & Setters
		
		public function get NumberSpriteHeight():Number
		{
			return _NumberSpriteHeight;
		}
		
		// Timers

		private function InitDisplayTimer(pMilliseconds:Number):void
		{
			_DisplayTimer = new Timer(_Turns.DisplayTimerInterval, pMilliseconds / _Turns.DisplayTimerInterval);
			_DisplayTimer.addEventListener(TimerEvent.TIMER_COMPLETE, OnDisplayTimerComplete, false, 0, true);
		}

		private function OnDisplayTimerComplete(pEvent:TimerEvent):void 
		{
			Hide(_NumberSprite);
			StartTimer(_IntervalTimer);
			ResetTimer(_DisplayTimer);
		}
		
		private function InitIntervalTimer(pMilliseconds:Number):void
		{
			_IntervalTimer = new Timer(_Turns.IntervalTimerInterval, pMilliseconds / _Turns.IntervalTimerInterval);
			_IntervalTimer.addEventListener(TimerEvent.TIMER_COMPLETE, OnIntervalTimerComplete, false, 0, true);
		}

		private function OnIntervalTimerComplete(pEvent:TimerEvent):void 
		{
			_IntervalTimer.reset();
			if (!isNaN(_RightAnswer) && !_Answered)
			{
				++_WrongAnswers;
			}
			_Parent.UpdateScoreDisplay(_RightAnswers, _WrongAnswers);
			_Parent.UpdateProgressBar((_Turn + 1) / _Turns.TurnsPerRound * 100);
			StartTurn();
		}
	}
}