package com.learningrx.AttentionArrows
{
	import flash.display.Sprite;
	import flash.display.Stage;
	import flash.events.*;
	import flash.utils.Timer;
	import flash.utils.*;

	import com.learningrx.*
	import com.learningrx.Screens.*
	
	public class AttentionArrows extends Game
	{
		private var _GlobalVolume:Number;

		private var _TurnDetails:Object;
		private var _Metronome:Metronome;
		private var _ResultsText:ResultsText;
		private var _Arrow:Arrow;
		private var _Distractions:Sprite;
		private var _ArrowKeyHandler:ArrowKeyHandler;
		private var _AltArrows:Boolean = false;
		private var _Answered:Boolean;
		private var _ConsecutiveRightAnswers:Number;
		private var _ConsecutiveWrongAnswers:Number;
		
		public function AttentionArrows(pParent:Framework)
		{
			super(pParent, 'AttentionArrows', com.learningrx.AttentionArrows.Turns);
			_Arrow = new Arrow(this);
			_Metronome = new Metronome(this);
			_Distractions = new com.learningrx.AttentionArrows.Distractions(this);
			_ArrowKeyHandler = new ArrowKeyHandler(this);
			Turns.Game = this;
			_GlobalVolume = Turns.MinimumVolume;
			_TurnDetails = new Object();
			this.mouseChildren = false;
		}

		override public function StartRound(pLevel:Number, 
														pSublevel:Number, 
														pSpeed:Number):void
		{
			ResetEverything();
			_Level = pLevel;
			_Sublevel = pSublevel;
			_Speed = pSpeed;
			_TurnDetails.TurnsPerRound = Turns.GetArrowsPerRound(_Speed);
			_Parent.ShowScoreAndDivider(true);
		}
		
		override public function OnStartRoundButtonClicked():void
		{
			super.OnStartRoundButtonClicked();
			var audioDistractions:Boolean = Turns.GetDistractionDetails(_Level, _Sublevel).AudioDistractions &&
													  Turns.GetDistractionDetails(_Level, _Sublevel).ShowDistractions;
			// I kept getting error messages if I didn't do this 
			var playAudibleBeat:Boolean = (true == Turns.PlayAudibleBeat(_Level));
			_Metronome.Reset(_Speed, playAudibleBeat, audioDistractions);
			Show(_Metronome);
		}
		
		override public function ResetEverything():void
		{
			Hide(_Arrow, _ResultsText, _Distractions);
			_Metronome.Stop();
			_TurnDetails = new Object();
			_Answered = true;
			super.ResetEverything();
		}
		
		override public function EndRound():void
		{
			Hide(_Arrow, _Distractions);
			super.EndRound();
		}
			
		public function OnArrowKeyPressed(pDirection:String):void
		{
			_Answered = true;
			_ArrowKeyHandler.Disable();
			if (_Metronome.IsWithinClickWindow() && pDirection == _TurnDetails.Answer)
			{
				RightAnswer();
			}
			else
			{
				WrongAnswer();
			}
		}
		
		public function OnStartTurn():void
		{
			StartTurn();
		}
		
		public function OnMetronomeBeat():void
		{
			//
		}
		
		private function StartTurn():void
		{
			if (!_Answered)
			{
				WrongAnswer();
			}
			++_Turn;
			if (_Turn >= _TurnDetails.TurnsPerRound)
			{
				EndRound();
			}
			else
			{
				Hide(_Metronome);
				Show(_Arrow);
				Utilities.MoveChildToTopOfDisplayList(this, _Arrow);
				_TurnDetails = _Turns.GetTurnDetails(_Level, _Sublevel, _TurnDetails.Color, _TurnDetails.Orientation, 
				                                     _TurnDetails.Motion, _Speed, _Turn);
				CreateDistractions();
				_Arrow.Reset(_TurnDetails, false, false);
				_Parent.UpdateProgressBar(((_Turn + 1) / _TurnDetails.TurnsPerRound) * 100);
				_Answered = false;
				_ArrowKeyHandler.Enable();
			}
		}

		private function CreateDistractions()
		{
			var distractionDetails:Object = _Turns.GetDistractionDetails(_Level, _Sublevel);
			if (distractionDetails.ShowDistractions)
			{
				Show(_Distractions);
				_Distractions.Reset(distractionDetails);
			}
			else
			{
				Hide(_Distractions);
			}
		}

		private function RightAnswer():void
		{
			++_RightAnswers;
			++_ConsecutiveRightAnswers;
			_ConsecutiveWrongAnswers = 0;
			Turns.FeedbackCheck(_ConsecutiveWrongAnswers, _ConsecutiveRightAnswers);
			_Parent.UpdateScoreDisplay(_RightAnswers, _WrongAnswers);
		}
		
		private function WrongAnswer():void
		{
			_ConsecutiveRightAnswers = 0;
			++_WrongAnswers;
			++_ConsecutiveWrongAnswers;
			Turns.FeedbackCheck(_ConsecutiveWrongAnswers, _ConsecutiveRightAnswers);
			_Parent.UpdateScoreDisplay(_RightAnswers, _WrongAnswers);
		}
		
		public function get Speed():Number
		{
			return _Speed;
		}
		
		public function get GlobalVolume():Number
		{
			return _GlobalVolume;
		}
		
		public function set GlobalVolume(pVolume:Number):void
		{
			_GlobalVolume = pVolume;
		}

		public function get AltArrows():Boolean
		{
			return _AltArrows;
		}
		
		public function get Distractions():Sprite
		{
			return _Distractions;
		}
	}
}