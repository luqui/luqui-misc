package com.learningrx.AttentionArrows
{
	import flash.display.Sprite;
	import flash.events.*;
	import flash.utils.*;
	import flash.geom.ColorTransform;
	import flash.filters.*;	
	import flash.text.*;

	import com.learningrx.*;
	
	public class Metronome extends Sprite
	{
		private var _Parent:Game;
		private var _Height:Number = 150;
		private var _MetronomeTimer:Timer;
		private var _FadeoutTimer:Timer;
		private var _BeatClick:BeatClick = new BeatClick();
		private var _PlayAudibleBeat:Boolean;
		private var _PlayAudioDistractions:Boolean;
		private var _ClickWindow:Number;
		private var _MillisecondsPerBeat:Number;
		private var _TimerInterval:Number;
		private var _MetronomeTotalBeats:Number;
		private var _TimerIntervalsPerBeat:Number;
		private var _CountdownNumber:Number;
		private var _BeatDelayIntervals:Number;
		
		public function Metronome(pParent:Game)
		{
			_Parent = pParent;
			CreateTextField('blue');
			AddFilters();
		}
		
		public function Reset(pSpeed:Number,
									 pPlayAudibleBeat:Boolean = true,
									 pPlayAudioDistractions:Boolean = false):void
		{
			_MetronomeTotalBeats = Turns.GetArrowsPerRound(pSpeed) + 1;
			_MillisecondsPerBeat = Turns.GetMilliSecondsPerBeat(pSpeed);
			_TimerInterval = Turns.MetronomeTimerInterval;
			_TimerIntervalsPerBeat = _MillisecondsPerBeat / _TimerInterval;
			_BeatDelayIntervals = Math.round(_TimerIntervalsPerBeat / 2);
			_ClickWindow = Turns.GetClickWindow(_MillisecondsPerBeat) / _TimerInterval;
			_PlayAudibleBeat = pPlayAudibleBeat;
			_PlayAudioDistractions = pPlayAudioDistractions;
			InitMetronomeTimer(_MetronomeTotalBeats);
			InitFadeOutTimer(_MillisecondsPerBeat);
			StartCountdown();
		}
		
		public function Stop():void
		{
			if (null != _MetronomeTimer)
			{
				Utilities.StopTimer(_MetronomeTimer);
			}
			if (null != _FadeoutTimer)
			{
				Utilities.StopTimer(_FadeoutTimer);
			}
		}

		public function IsWithinClickWindow():Boolean
		{
			if (_MetronomeTimer != null)
			{
				return Math.abs(_TimerIntervalsPerBeat - (GetIntervalsSinceLastBeat() + _BeatDelayIntervals)) <= _ClickWindow;
			}
			return false;
		}

		private function GetIntervalsSinceLastBeat():Number
		{
         return _MetronomeTimer.currentCount % _TimerIntervalsPerBeat;
		}

		public function StartCountdown():void
		{
			Utilities.AddChildToDisplayList(this, _TextField);
			_CountdownNumber = 3;
			Utilities.StartTimer(_FadeOutTimer);
			Utilities.StartTimer(_MetronomeTimer);
			SetText(_CountdownNumber.toString(), _Height);
			Utilities.StartTimer(_FadeOutTimer);
		}

		private function SetText(pText:String,
										 pHeight:Number):void
		{
			var format:TextFormat = new TextFormat();
			format.size = pHeight;
			_TextField.defaultTextFormat = format;
			_TextField.alpha = 1;
			_TextField.text = pText;
			_TextField.x = (_Parent.BackgroundWidth - _TextField.textWidth) / 2;
			_TextField.y = (_Parent.ScoreAndDividerY - _TextField.textHeight) / 2;
		}
		
		private function OnMetronomeTimer(pEvent:TimerEvent):void 
		{
			if (_CountdownNumber > 0)
			{
				if (GetIntervalsSinceLastBeat() == 0)
				{
					SetText(_CountdownNumber.toString(), _Height);
					Utilities.StartTimer(_FadeOutTimer);
				}
				else if (GetIntervalsSinceLastBeat() == _BeatDelayIntervals)
				{
					PlayClick();
					--_CountdownNumber;
				}
			}
			else if (0 == _CountdownNumber)
			{
				if (GetIntervalsSinceLastBeat() == 0)
				{
					SetText('Get ready...', _Height * .25);
					Utilities.RestartTimer(_MetronomeTimer); // Countdown is over. So we restart from 0;
				}
				else if (GetIntervalsSinceLastBeat() == _BeatDelayIntervals)
				{
					PlayClick();
					Utilities.RemoveChildFromDisplayList(this, _TextField);
					--_CountdownNumber;
				}
			}
			else if (GetIntervalsSinceLastBeat() == 0)
			{
				_Parent.OnStartTurn();
			}
			else if (GetIntervalsSinceLastBeat() == _BeatDelayIntervals)
			{
				_Parent.OnMetronomeBeat();
				PlayClick();
			} 
			else if (_PlayAudioDistractions && Utilities.RandRange(0, _TimerIntervalsPerBeat) == 0)
			{
				_Parent.Distractions.PlayRandomAudioDistraction();
			}
		}
		
		private function OnMetronomeTimerComplete(pEvent:TimerEvent):void 
		{
			_Parent.EndRound();
		}

		private function PlayClick():void 
		{
			if (_PlayAudibleBeat)
			{
				_BeatClick.play();
			}
		}

		private function OnFadeOutTimer(pEvent:TimerEvent):void 
		{
			_TextField.alpha = 1 - _FadeOutTimer.currentCount / _FadeOutTimer.repeatCount;
		}
		
		private function OnFadeOutTimerComplete(pEvent:TimerEvent):void 
		{
			Utilities.ResetTimer(_FadeOutTimer);
		}

		private function CreateTextField(pColor:String):void
		{
			_TextField = new TextField();
			_TextField.antiAliasType = flash.text.AntiAliasType.ADVANCED;
			_TextField.embedFonts = true;
			_TextField.autoSize = TextFieldAutoSize.LEFT
			var format:TextFormat = new TextFormat();
			format.font = 'Arial Rounded MT Bold';
			format.color = Turns.GetArrowColorValue(pColor);
			format.size = _Height;
			_TextField.defaultTextFormat = format;
			_TextField.text = '';
			_TextField.selectable = false;
		}
		
		private function AddFilters():void
		{
			var bevelFilter:BevelFilter = new BevelFilter();
			bevelFilter.distance = 2;
			bevelFilter.angle = 45;
			bevelFilter.highlightColor = 0xFFFFFF;
			bevelFilter.highlightAlpha = .8;
			bevelFilter.shadowColor = 0x000000;
			bevelFilter.shadowAlpha = .8;
			bevelFilter.blurX = 2;
			bevelFilter.blurY = 2;
			bevelFilter.strength = 1;
			bevelFilter.quality = BitmapFilterQuality.HIGH;
			bevelFilter.type = BitmapFilterType.INNER;
			bevelFilter.knockout = false;
			var dropShadow:DropShadowFilter = new DropShadowFilter();
			dropShadow.distance = 5;
			dropShadow.color = 0x000000;
			dropShadow.angle = 45;
			dropShadow.alpha = .5;
			dropShadow.blurX = 5;
			dropShadow.blurY = 5;
			dropShadow.quality = BitmapFilterQuality.HIGH;
			dropShadow.knockout = false;
			this.filters = [bevelFilter, dropShadow];
		}

		private function InitFadeOutTimer(pFadeOutMilliSeconds:Number):void
		{
			_FadeOutTimer = new Timer(_TimerInterval, pFadeOutMilliSeconds / _TimerInterval - 2);
			_FadeOutTimer.addEventListener(TimerEvent.TIMER, OnFadeOutTimer);
			_FadeOutTimer.addEventListener(TimerEvent.TIMER_COMPLETE, OnFadeOutTimerComplete);
		}

		private function InitMetronomeTimer(pTotalBeats:Number):void
		{
			_MetronomeTimer = new Timer(_TimerInterval, _TimerIntervalsPerBeat * pTotalBeats);
			_MetronomeTimer.addEventListener(TimerEvent.TIMER, OnMetronomeTimer);
			_MetronomeTimer.addEventListener(TimerEvent.TIMER_COMPLETE, OnMetronomeTimerComplete);
		}
	}
}