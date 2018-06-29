import React from 'react'
import Link from 'gatsby-link'
import styled from "react-emotion"

require("./global.css");
require("./theme.css");

const Header = styled.header`
  margin: 3vw auto;
  padding-left: 3vw;
  padding-right: 3vw;
  display: flex;
  justify-content: center;
  width: auto;
  max-width: 1280px;
`;

const HeaderBoxLeft = styled.div`
  flex: 1 1 0px;
  margin-bottom: 100px;
`;

const HeaderBoxRight = styled.div`
  flex: 1 1 0px;
  text-align: right;
  justify-content: flex-end;
`;

const Main = styled.main`
  max-width: 1000px;
  margin: auto;
  padding: 3vw;
`;

const Monic = styled.span`
  font-weight: 400;
  letter-spacing: 2px;
`;

const HeadH1 = styled.h1`
  font-family: europa, Nunino, sans-serif;
  font-weight: 700;
  font-style: normal;
  font-size: 20px;
  letter-spacing: .04em;
  text-transform: none;
  line-height: 1em;
`;

const HeadItem = styled.div`
  display: inline-block;
  font-family: Arial,Helvetica,sans-serif;
  font-weight: 400;
  font-style: normal;
  font-size: 16px;
  letter-spacing: .05em;
  text-transform: none;
  line-height: 1em;
  text-rendering: optimizeLegibility;
  box-flex: 1;
  flex: 1 1 0px;
`;

const HeadLink = styled.a`
  text-decoration: none;
  color: #0a2e6b;
`;

function Link_({ to, children }) {
  return (
    <Link
      style={{textDecoration: 'none', color: '#0a2e6b'}}
      to={to}
    >{children}</Link>
  );
}

export default class Template extends React.Component {
  render() {
    const { children } = this.props

    return (
      <div>
        <Header>
          <HeaderBoxLeft>
            <HeadH1>
              <HeadLink href="https://www.monic.co">
                <Monic>MONIC</Monic>
              </HeadLink>
            </HeadH1>
          </HeaderBoxLeft>
          <HeaderBoxRight>
            <HeadItem>
              <HeadLink href="https://www.monic.co/about">About</HeadLink>
            </HeadItem>
            <HeadItem style={{marginLeft: '18px'}}>
              <Link_ to="/">Blog</Link_>
            </HeadItem>
            <HeadItem style={{marginLeft: '18px'}}>
              <HeadLink href="https://www.monic.co/contact">Contact</HeadLink>
            </HeadItem>
          </HeaderBoxRight>
        </Header>
        <Main>{children()}</Main>
      </div>
    )
  }
}
