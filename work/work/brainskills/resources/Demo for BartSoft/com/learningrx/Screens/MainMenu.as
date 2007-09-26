package com.learningrx.Screens
{
	import flash.display.Sprite;
	import flash.display.SimpleButton; 
	import flash.events.*;
	import flash.net.*;
	import flash.text.TextField;
	import flash.text.TextFormat;
	import flash.text.TextFormatAlign;
	import flash.text.TextFieldAutoSize;
	import flash.text.AntiAliasType;
	
	import com.learningrx.*
	import com.learningrx.Demo.*;
	
	public class MainMenu extends Sprite
	{
		private var _Width:Number;
		private var _Height:Number;
		private var _Leading:Number = 20;

		private var _Parent:Framework;
		private var _Background:MainMenuBackground;
		private var _DemoMenu:DemoMenu;
		private var _NextButton:NextButton;
		private var _IntroText:TextField;
		private var _HeaderText:TextField;
		
		public function MainMenu(pParent:Framework)
		{
			_Parent = pParent;
			_Width = _Parent.GAME_WIDTH - 50;
			_Height = _Parent.GAME_HEIGHT;
			InitHeaderText();
			InitIntroText();
			InitStuff();
			Show(_Background, _NextButton, _IntroText, _HeaderText);
		}
		
		private function ShowMenuScreen(...args)
		{
			Hide(_IntroText, _NextButton);
			Show(_DemoMenu);
		}
		
		private function InitStuff()
		{
			_Background = new MainMenuBackground();
			_Background.x = 0;
			_Background.y = 0;
			_Background.alpha = .1;
			_NextButton = new NextButton();
			_NextButton.addEventListener(MouseEvent.CLICK, ShowMenuScreen);
			_NextButton.x = _Width - 40;
			_NextButton.y = _Height - 14;
			_DemoMenu = new DemoMenu(_Parent);
			_DemoMenu.x = (_Width - _DemoMenu.width) / 2;
			_DemoMenu.y = _HeaderText.y + _HeaderText.textHeight + _Leading;
		}
		
		private function InitHeaderText()
		{
			_HeaderText = new TextField;
			_HeaderText.width = _Width * .8;
			_HeaderText.selectable = false;
			_HeaderText.multiline = true;
			_HeaderText.wordWrap = true;
			_HeaderText.antiAliasType = AntiAliasType.ADVANCED;
			_HeaderText.embedFonts = true;
			_HeaderText.autoSize = TextFieldAutoSize.CENTER;
			format = new TextFormat();
			format.font = 'Smudger LET';
			format.size = 48;
			format.color = 0xFFFFFF;
			format.leading = 6;
			format.align = TextFormatAlign.CENTER;
			_HeaderText.defaultTextFormat = format;
			_HeaderText.x = (_Width - _HeaderText.width) / 2;
			_HeaderText.y = 62;
			_HeaderText.text = 'Welcome to eLearningrx.com\'s\nBrainskills Digital!'
		}
		
		private function InitIntroText()
		{
			_IntroText = new TextField;
			_IntroText.width = _Width * .6;
			_IntroText.selectable = false;
			_IntroText.multiline = true;
			_IntroText.wordWrap = true;
			_IntroText.antiAliasType = AntiAliasType.ADVANCED;
			_IntroText.embedFonts = true;
			_IntroText.autoSize = TextFieldAutoSize.CENTER;
			format = new TextFormat();
			format.font = 'Arial Rounded MT Bold';
			format.size = 24;
			format.color = 0xFFFFFF;
			format.leading = format.size / 2;
			format.align = TextFormatAlign.CENTER;
			_IntroText.defaultTextFormat = format;
			_IntroText.x = (_Width - _IntroText.width) / 2;
			_IntroText.y = _HeaderText.y + _HeaderText.textHeight + _Leading * 3;
			_IntroText.text = 'Brainskills Digital exercises train cognitive skills areas that help your brain work more efficiently and quickly. These exercises will improve memory, processing speed, comprehension, reasoning, and more!'
		}
		
		private function Show(...args):void
		{
			for (var i:Number = 0; i < args.length; ++i)
			{
				Utilities.AddChildToDisplayList(this, args[i]);
			}
		}

		private function Hide(...args):void
		{
			for (var i:Number = 0; i < args.length; ++i)
			{
				Utilities.RemoveChildFromDisplayList(this, args[i]);
			}
		}
	}
}