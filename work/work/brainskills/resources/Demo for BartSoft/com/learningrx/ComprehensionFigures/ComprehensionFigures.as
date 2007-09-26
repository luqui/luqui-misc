package com.learningrx.ComprehensionFigures
{
	import flash.display.*;
	import flash.events.MouseEvent;
	import flash.utils.Timer;
	import flash.events.TimerEvent;

	import com.learningrx.*;
	import com.learningrx.Screens.*;
	
	public class ComprehensionFigures extends Game
	{
		private var _FindBox:FindBox;
		private var _KeyBox:KeyBox;
		private var _KeyBoxMask:Sprite;
		private var _AnswerBoxes:Array = new Array();
		private var _TurnDetails:Object;
		private var _Key:Array = new Array();
		private var _CorrectAnswerBoxNumber:Number;
		private var _TurnTimer:Timer;
		private var _RoundTimer:Timer;

		public function ComprehensionFigures(pParent:Framework)
		{
			super(pParent, 'ComprehensionFigures', com.learningrx.ComprehensionFigures.Turns);
			InitRoundTimer();
			CreateBoxes();
		}

		override public function StartRound(pLevel:Number, 
														pSublevel:Number, 
														pSpeed:Number):void
		{
			super.StartRound(pLevel, pSublevel, pSpeed);
			PositionAnswerBoxes();
			_Parent.ShowScoreAndDivider(true);
			InitTurnTimer(_RoundDetails.SecondsPerTurn);
			UpdateKeyBox();
			Show(_FindBox);
		}
		
		override public function OnStartRoundButtonClicked():void
		{
			super.OnStartRoundButtonClicked();
			_SecondsElapsedInRound = 0;
			RestartTimer(_RoundTimer);
			ShowAnswerBoxes();
			StartTurn();
		}
		
		override public function EndRound():void
		{
			HideAnswerBoxes();
			_KeyBox.Hide();
			super.EndRound();
		}
			
		override public function ResetEverything():void
		{
			ResetTimer(_TurnTimer);
			HideAnswerBoxes();
			_FindBox.ClearRule();
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
				_TurnDetails = Turns.CreateTurn(this, _RoundDetails, _Key);
				_FindBox.DisplayRule(_TurnDetails, _RoundDetails);
				_CorrectAnswerBoxNumber = Utilities.RandRange(0, 3);
				InitAnswerBoxes();
				StartTimer(_TurnTimer);
				EnableAnswerBoxes();
				CheckForHidingKey();
			}
		}
		
		public function AnswerBoxClicked(pAnswerBox:AnswerBox):void
		{
			ResetTimer(_TurnTimer);
			DisableAnswerBoxes();
			if (_AnswerBoxes[_CorrectAnswerBoxNumber] == pAnswerBox)
			{
				++_RightAnswers;
				Utilities.PauseTimer(Turns.RightAnswerPauseSeconds, StartTurn);
			}
			else
			{
				++_WrongAnswers;
				pAnswerBox.Clicklight(false);
				_FindBox.DisplayRule(_TurnDetails, _RoundDetails);
				Utilities.PauseTimer(Turns.WrongAnswerPauseSeconds, StartTurn);
			}
			_Parent.UpdateScoreDisplay(_RightAnswers, _WrongAnswers);
			_AnswerBoxes[_CorrectAnswerBoxNumber].Clicklight(true);
		}

		public function PositionAnswerBoxes():void
		{
			if (_AnswerBoxes.length == 0)
			{
				return; //scram if the Answer Boxes haven't been created yet
			}
			var topBorder:Number = _KeyBox.y + _KeyBox.height;
			var verticalMargin:Number = Math.round((_Parent.ScoreAndDividerY - topBorder - 2 * _AnswerBoxes[0].height) / 3);
			var horizontalMargin:Number = Math.round((BackgroundWidth - 2 * _AnswerBoxes[0].width) / 3);
			for (var i:Number = 0; i < _AnswerBoxes.length; ++i)
			{
				if (i < 2)
				{
					_AnswerBoxes[i].y = topBorder + verticalMargin;
				}
				else
				{
					_AnswerBoxes[i].y = _AnswerBoxes[0].y + _AnswerBoxes[0].height + verticalMargin;
				}
				_AnswerBoxes[i].x = horizontalMargin + (i % 2) * (_AnswerBoxes[0].width + horizontalMargin);
			}
		}
		
		private function UpdateKeyBox():void
		{
			if ('self' != _RoundDetails.Represent)
			{
				_Key = Turns.CreateKey(_RoundDetails.NumberOfFigures);
				_KeyBox.InitKey(_Key);
				_KeyBox.FadeKeyIn();
			}
			else
			{
				_KeyBox.FadeKeyOut();
			}
		}
		
		private function EnableAnswerBoxes()
		{
			for (var i:Number = 0; i < Turns.NumberOfAnswerBoxes; ++i)
			{
				_AnswerBoxes[i].Enable();
			}
		}
		
		private function DisableAnswerBoxes()
		{
			for (var i:Number = 0; i < Turns.NumberOfAnswerBoxes; ++i)
			{
				_AnswerBoxes[i].Disable();
			}
		}
		
		private function CheckForHidingKey()
		{
			if (!isNaN(_RoundDetails.TurnToHideKey) && _Turn >= _RoundDetails.TurnToHideKey)
			{
				_KeyBox.FadeKeyOut();
			}
		}
		
		private function ShowAnswerBoxes()
		{
			for (var i:Number = 0; i < Turns.NumberOfAnswerBoxes; ++i)
			{
				Show(_AnswerBoxes[i]);
			}
		}
		
		private function HideAnswerBoxes()
		{
			for (var i:Number = 0; i < Turns.NumberOfAnswerBoxes; ++i)
			{
				Hide(_AnswerBoxes[i]);
			}
		}
		
		private function CreateBoxes():void
		{
			_FindBox = new FindBox(this);
			_FindBox.x = 0;
			_FindBox.y = 0;
			_KeyBox = new KeyBox(this, _FindBox.TrueHeight);
			_KeyBoxMask = new Sprite;
			_KeyBox.x = 1;
			_KeyBox.y = _FindBox.TrueHeight;
			_KeyBoxMask.x = _KeyBox.x;
			_KeyBoxMask.y = _KeyBox.y;
			_KeyBoxMask.graphics.beginFill(0xFF0000);
			_KeyBoxMask.graphics.drawRect(0, 0, _KeyBox.width, _KeyBox.height);
			_KeyBox.mask = _KeyBoxMask;
			Show(_KeyBox, _KeyBoxMask);
			_KeyBox.Hide();
			_AnswerBoxes = new Array();
			for (var i:Number = 0; i < Turns.NumberOfAnswerBoxes; ++i)
			{
				_AnswerBoxes.push(new AnswerBox(this));
			}
		}
		
		private function CheckForFindFade(pSecondsElapsed)
		{
			if (!isNaN(_RoundDetails.SecondsToHideFindText))
			{
				if (_TurnTimer.currentCount * 1000 / Turns.TurnTimerInterval >= _RoundDetails.SecondsToHideFindText)
				{
					_FindBox.FadeFindOut();
				}
			}
		}
		
		private function InitAnswerBoxes():void
		{
			var lastChosenDistractor:Number = 0;
			
			for (var i:Number = 0; i < Turns.NumberOfAnswerBoxes; ++i)
			{
				if (i == _CorrectAnswerBoxNumber)
				{
					_AnswerBoxes[i].Draw(_TurnDetails.Figures, _TurnDetails.Positions);
				}
				else
				{
					var distractor:Object = _TurnDetails.distractors[lastChosenDistractor];
					_AnswerBoxes[i].Draw(distractor.Figures, distractor.Positions);
					++lastChosenDistractor;
				}
			}
		}
		
		private function InitTurnTimer(pSeconds:Number):void
		{
			_TurnTimer = new Timer(Turns.TurnTimerInterval, pSeconds * (1000 / Turns.TurnTimerInterval));
			_TurnTimer.addEventListener(TimerEvent.TIMER, OnTurnTimer);
			_TurnTimer.addEventListener(TimerEvent.TIMER_COMPLETE, OnTurnTimerComplete);
		}

		private function OnTurnTimer(pEvent:TimerEvent):void 
		{
			_Parent.UpdateProgressBar(_TurnTimer.currentCount / _TurnTimer.repeatCount * 100);
			CheckForFindFade(_TurnTimer.currentCount / (1000 / Turns.TurnTimerInterval));
		}
		
		private function OnTurnTimerComplete(pEvent:TimerEvent):void 
		{
         DisableAnswerBoxes();
			ResetTimer(_TurnTimer);
			++_WrongAnswers;
			_Parent.UpdateScoreDisplay(_RightAnswers, _WrongAnswers);
			for (var i:Number = 0; i < Turns.NumberOfAnswerBoxes; ++ i)
			{
				_AnswerBoxes[i].Clicklight(_CorrectAnswerBoxNumber == i);
			}
			Utilities.PauseTimer(Turns.WrongAnswerPauseSeconds, StartTurn);
		}
		
		protected function InitRoundTimer():void
		{
			_RoundTimer = new Timer(Game.ROUND_TIMER_INTERVAL);
			_RoundTimer.addEventListener(TimerEvent.TIMER, OnRoundTimer);
		}

		protected function OnRoundTimer(pEvent:TimerEvent):void 
		{
			++_SecondsElapsedInRound;
		}
	}
}