package com.learningrx.ComprehensionFigures
{
	import flash.display.Shape;
	import flash.text.TextField;
	import flash.text.TextFormat;
	import flash.text.TextFormatAlign;
	import flash.text.TextFieldAutoSize;
	import flash.text.AntiAliasType;
	import flash.utils.Timer;
	import flash.events.TimerEvent;
	
	import com.learningrx.*;
	import com.learningrx.Screens.*;

	
	public class FindBox extends Screen
	{
		private const FIND_FADE_SECONDS:Number = .3;
		private const FIND_FADE_OUT:String = "out";
		private const FIND_FADE_IN:String = "in";
		private const FIND_TIMER_INTERVAL:Number = 10; // lower = smoother fade

		private var _FindFadeTimer:Timer;
		private var _FindFadeSeconds:Number = FIND_FADE_SECONDS;
		private var _FindFadeDirection:String = FIND_FADE_OUT;
		private var _FindTextField:TextField;
		private var _FindLabel:TextField;
		private var _TrueHeight:Number;
		
		public function FindBox(pParent:Game)
		{
			super(pParent);
			CreateBackground();
			CreateFindLabel();
			CreateFindTextField();
			_TrueHeight = 70;
		}
		
		public function get TrueHeight():Number
		{
			return _TrueHeight;
		}

		public function ClearRule():void
		{
			_FindTextField.text = '';
		}

		public function DisplayRule(pTurn:Object,
											 pRule:Object):void
		{
			_FindTextField.alpha = 1;
			_FindTextField.text = _Parent.Turns.GetFindText(pTurn, pRule);
			_FindTextField.y = _FindLabel.y + (_FindLabel.height - _FindTextField.textHeight) / 2;
		}

		public function FadeFindOut():void
		{
         InitFindFadeTimer(FIND_FADE_SECONDS, FIND_FADE_OUT);
			StartFindFadeTimer();
		}

		public function FadeFindIn():void
		{
         InitFindFadeTimer(FIND_FADE_SECONDS, FIND_FADE_IN);
			StartFindFadeTimer();
		}
		
		protected function CreateBackground():void
		{
			this.graphics.beginFill(0x00CC00, .3)
			this.graphics.lineStyle(0, 0x00CC00, 0, true, "none", "none", "round");
			this.graphics.drawRoundRect(0, 0, 890, 76, 30, 30);
			this.graphics.endFill(); 
			var dividingLine = new DividingLine(888);
			Utilities.AddChildToDisplayList(this, dividingLine);
			dividingLine.y = 70;
			dividingLine.x = -1;
			var square:Shape = new Shape();
			square.graphics.lineStyle(0, 0xFF0000, 1);
			square.graphics.beginFill(0xFF0000, 1);
			square.graphics.drawRect(0, 0, 890, 70);
			square.graphics.endFill();
			square.x = this.x;
			square.y = this.y;
			this.mask = square;
			Utilities.AddChildToDisplayList(_Parent, square);
		}
			
		protected function CreateFindLabel():void
		{
			_FindLabel = new TextField();
			_FindLabel.antiAliasType = AntiAliasType.ADVANCED;
			_FindLabel.embedFonts = true;
			_FindLabel.autoSize = TextFieldAutoSize.LEFT;
			format = new TextFormat();
			format.font = 'Arial';
			format.size = 20;
			format.color = 0xFFFFFF;
			format.align = TextFormatAlign.LEFT;
			_FindLabel.defaultTextFormat = format;
			_FindLabel.text = 'FIND:';
			_FindLabel.selectable = false;
			_FindLabel.x = 6;
			_FindLabel.y = 20;
			Utilities.AddChildToDisplayList(this, _FindLabel);
		}
			
		protected function CreateFindTextField():void
		{
			_FindTextField = new TextField();
			_FindTextField.width = this.width - 100;
			_FindTextField.selectable = false;
			_FindTextField.multiline = true;
			_FindTextField.wordWrap = true;
			_FindTextField.antiAliasType = AntiAliasType.ADVANCED;
			_FindTextField.embedFonts = true;
			_FindTextField.autoSize = TextFieldAutoSize.LEFT;
			format = new TextFormat();
			format.font = 'Arial';
			format.size = 20;
			format.color = 0xFFFFFF;
			format.align = TextFormatAlign.LEFT;
			_FindTextField.defaultTextFormat = format;
			_FindTextField.text = '';
			_FindTextField.x = _FindLabel.x + _FindLabel.textWidth + 20;
			_FindTextField.y = 20;
			Utilities.AddChildToDisplayList(this, _FindTextField);
			
		}
			
		protected function InitFindFadeTimer(pSeconds:Number,
														 pDirection:String):void
		{
			_FindFadeSeconds = pSeconds;
			_FindFadeDirection = pDirection;
			_FindFadeTimer = new Timer(FIND_TIMER_INTERVAL, _FindFadeSeconds * 1000 / FIND_TIMER_INTERVAL);
			_FindFadeTimer.addEventListener(TimerEvent.TIMER, OnFindFadeTimer);
			_FindFadeTimer.addEventListener(TimerEvent.TIMER_COMPLETE, OnFindFadeTimerComplete);
		}

		protected function StartFindFadeTimer():void
		{
         _FindFadeTimer.start();
		}

		protected function OnFindFadeTimerComplete(pEvent:TimerEvent):void 
		{
         _FindFadeTimer.reset();
			if (FIND_FADE_IN == _FindFadeDirection)
			{
				_FindTextField.alpha = 1;
			}
			else
			{
				_FindTextField.alpha = 0;
			}
		}
		
		protected function OnFindFadeTimer(pEvent:TimerEvent):void
		{
			if (FIND_FADE_IN == _FindFadeDirection)
			{
				_FindTextField.alpha = _FindFadeTimer.currentCount / _FindFadeTimer.repeatCount;
			}
			else
			{
				_FindTextField.alpha = 1 - _FindFadeTimer.currentCount / _FindFadeTimer.repeatCount;
			}
		}
	}
}